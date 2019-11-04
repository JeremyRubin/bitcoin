// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <txmempool.h>

#include <consensus/consensus.h>
#include <consensus/tx_verify.h>
#include <consensus/validation.h>
#include <optional.h>
#include <validation.h>
#include <policy/policy.h>
#include <policy/fees.h>
#include <policy/settings.h>
#include <reverse_iterator.h>
#include <util/system.h>
#include <util/moneystr.h>
#include <util/time.h>

CTxMemPoolEntry::CTxMemPoolEntry(const CTransactionRef& _tx, const CAmount& _nFee,
                                 int64_t _nTime, unsigned int _entryHeight,
                                 bool _spendsCoinbase, int64_t _sigOpsCost, LockPoints lp)
    : tx(_tx), parents(1), children(1), nFee(_nFee), nTxWeight(GetTransactionWeight(*tx)), nUsageSize(RecursiveDynamicUsage(tx)), nTime(_nTime), entryHeight(_entryHeight),
    spendsCoinbase(_spendsCoinbase), sigOpCost(_sigOpsCost), lockPoints(lp), m_epoch(0)
{
    nCountWithDescendants = 1;
    nSizeWithDescendants = GetTxSize();
    nModFeesWithDescendants = nFee;

    feeDelta = 0;

    nCountWithAncestors = 1;
    nSizeWithAncestors = GetTxSize();
    nModFeesWithAncestors = nFee;
    nSigOpCostWithAncestors = sigOpCost;
}

void CTxMemPoolEntry::UpdateFeeDelta(int64_t newFeeDelta)
{
    nModFeesWithDescendants += newFeeDelta - feeDelta;
    nModFeesWithAncestors += newFeeDelta - feeDelta;
    feeDelta = newFeeDelta;
}

void CTxMemPoolEntry::UpdateLockPoints(const LockPoints& lp)
{
    lockPoints = lp;
}

size_t CTxMemPoolEntry::GetTxSize() const
{
    return GetVirtualTransactionSize(nTxWeight, sigOpCost);
}

// Update the given tx for any in-mempool descendants.
// Assumes that setMemPoolChildren is correct for the given tx and all
// descendants.
//
void CTxMemPool::UpdateForDescendants(txiter update_it, cacheMap& cache, const std::unordered_set<uint256, SaltedTxidHasher>& exclude) {
    const auto epoch = GetFreshEpoch();
    int64_t modify_size = 0;
    CAmount modify_fee = 0;
    int64_t modify_count = 0;
    const CTxMemPoolEntry::relatives& direct_children = update_it->GetMemPoolChildrenConst();
    std::vector<txiter> update_cache;
    for (const CTxMemPoolEntry& direct_child : direct_children) {
        const txiter t = mapTx.iterator_to(direct_child);
        update_cache.emplace_back(t);
        already_touched(t);
    }
    size_t already_traversed = 0;
    while (already_traversed < update_cache.size()) {
        // rotate to the front OR drop
        const txiter child_it = update_cache.back();
        const CTxMemPoolEntry& child = *child_it;
        // Only put back in if we want it later for the cache
        // & collect stats
        if (exclude.count(child.GetTx().GetHash())) {
            update_cache.pop_back();
        } else {
            std::swap(update_cache[already_traversed++], update_cache.back());
            modify_size += child.GetTxSize();
            modify_fee += child.GetModifiedFee();
            modify_count++;
            mapTx.modify(child_it, update_ancestor_state(update_it->GetTxSize(), update_it->GetModifiedFee(), 1, update_it->GetSigOpCost()));

        }

        // N.B. grand_children may also be children
        const CTxMemPoolEntry::relatives& grand_children = child.GetMemPoolChildrenConst();
        for (const CTxMemPoolEntry& grand_child : grand_children) {
            const txiter grand_child_it = mapTx.iterator_to(grand_child);
            if (already_touched(grand_child_it)) continue;
            cacheMap::iterator cached_great_grand_children = cache.find(grand_child_it);
            if (cached_great_grand_children != cache.end()) {
                for (const txiter great_grand_child : cached_great_grand_children->second) {
                    if (already_touched(great_grand_child)) continue;
                    // Not needed to check excluded-- if it's in the cache it's not excluded
                    update_cache.emplace_back(great_grand_child);
                    // place on the back and then swap into the already_traversed index
                    // so we don't walk it ourselves
                    std::swap(update_cache[already_traversed++], update_cache.back());
                }
            } else {
                // Schedule for later processing
                update_cache.emplace_back(grand_child_it);
            }
        }
    }
    if (!update_cache.empty()) cache.emplace(update_it, std::move(update_cache));
    mapTx.modify(update_it, update_descendant_state(modify_size, modify_fee, modify_count));
};

// vHashesToUpdate is the set of transaction hashes from a disconnected block
// which has been re-added to the mempool.
// for each entry, look for descendants that are outside vHashesToUpdate, and
// add fee/size information for such descendants to the parent.
// for each such descendant, also update the ancestor state to include the parent.
void CTxMemPool::UpdateTransactionsFromBlock(const std::vector<uint256> &vHashesToUpdate)
{
    AssertLockHeld(cs);
    // For each entry in vHashesToUpdate, store the set of in-mempool, but not
    // in-vHashesToUpdate transactions, so that we don't have to recalculate
    // descendants when we come across a previously seen entry.
    cacheMap mapMemPoolDescendantsToUpdate;

    // Use a set for lookups into vHashesToUpdate (these entries are already
    // accounted for in the state of their ancestors)
    std::unordered_set<uint256, SaltedTxidHasher> setAlreadyIncluded(vHashesToUpdate.begin(), vHashesToUpdate.end());

    // Iterate in reverse, so that whenever we are looking at a transaction
    // we are sure that all in-mempool descendants have already been processed.
    // This maximizes the benefit of the descendant cache and guarantees that
    // setMemPoolChildren will be updated, an assumption made in
    // UpdateForDescendants.
    for (const uint256 &hash : reverse_iterate(vHashesToUpdate)) {
        // calculate children from mapNextTx
        txiter it = mapTx.find(hash);
        if (it == mapTx.end()) {
            continue;
        }
        auto children = mapNextTx.find(hash);
        // no children to update...
        if (children == mapNextTx.end()) continue;
        // First calculate the children, and update setMemPoolChildren to
        // include them, and update their setMemPoolParents to include this tx.
        // we cache the in-mempool children to avoid duplicate updates
        {
            const auto epoch = GetFreshEpoch();
            for (auto& child : children->second) {
                const uint256 &childHash = child.second->GetTx().GetHash();
                // We can skip updating entries we've encountered before or that
                // are in the block (which are already accounted for).
                if (!already_touched(child.second) && !setAlreadyIncluded.count(childHash)) {
                    UpdateChild(it, child.second, true);
                    UpdateParent(child.second, it, true);
                }
            }
        } // release epoch guard for UpdateForDescendants
        UpdateForDescendants(it, mapMemPoolDescendantsToUpdate, setAlreadyIncluded);
    }
}

bool CTxMemPool::CalculateMemPoolAncestors(const CTxMemPoolEntry &entry, vecEntries &ancestors, uint64_t limitAncestorCount, uint64_t limitAncestorSize, uint64_t limitDescendantCount, uint64_t limitDescendantSize, std::string &errString, bool fSearchForParents /* = true */) const
{
    assert(ancestors.size() == 0);
    const CTransaction &tx = entry.GetTx();
    const auto epoch = GetFreshEpoch();
    if (fSearchForParents) {
        // Get parents of this transaction that are in the mempool
        // GetMemPoolParents() is only valid for entries in the mempool, so we
        // iterate mapTx to find parents.
        for (unsigned int i = 0; i < tx.vin.size(); i++) {
            Optional<txiter> piter = GetIter(tx.vin[i].prevout.hash);
            if (already_touched(piter)) continue;
            ancestors.push_back(*piter);
            if (ancestors.size() + 1 > limitAncestorCount) {
                errString = strprintf("too many unconfirmed parents [limit: %u]", limitAncestorCount);
                return false;
            }
        }
    } else {
        // If we're not searching for parents, we require this to be an
        // entry in the mempool already.
        txiter it = mapTx.iterator_to(entry);
        const auto& ref_parents = it->GetMemPoolParentsConst();
        ancestors.reserve(ref_parents.size());
        for (const auto& parent: ref_parents) {
            ancestors.emplace_back(mapTx.iterator_to(parent));
            // touch before walking so we don't add a duplicate
            already_touched(ancestors.back());
        }
    }


    size_t totalSizeWithAncestors = entry.GetTxSize();

    size_t next_idx = 0;
    while (next_idx < ancestors.size()) {
        txiter stageit = ancestors[next_idx++];

        totalSizeWithAncestors += stageit->GetTxSize();

        if (stageit->GetSizeWithDescendants() + entry.GetTxSize() > limitDescendantSize) {
            errString = strprintf("exceeds descendant size limit for tx %s [limit: %u]", stageit->GetTx().GetHash().ToString(), limitDescendantSize);
            return false;
        } else if (stageit->GetCountWithDescendants() + 1 > limitDescendantCount) {
            errString = strprintf("too many descendants for tx %s [limit: %u]", stageit->GetTx().GetHash().ToString(), limitDescendantCount);
            return false;
        } else if (totalSizeWithAncestors > limitAncestorSize) {
            errString = strprintf("exceeds ancestor size limit [limit: %u]", limitAncestorSize);
            return false;
        }

        const CTxMemPoolEntry::relatives& setMemPoolParents = stageit->GetMemPoolParentsConst();
        for (auto pphash : setMemPoolParents) {
            auto phash = mapTx.iterator_to(pphash);
            // If this is a new ancestor, add it.
            if (already_touched(phash)) continue;
            ancestors.push_back(phash);
            if (ancestors.size() + 1 > limitAncestorCount) {
                errString = strprintf("too many unconfirmed ancestors [limit: %u]", limitAncestorCount);
                return false;
            }
        }
    }

    return true;
}

void CTxMemPool::UpdateAncestorsOf(bool add, txiter it, vecEntries &ancestors)
{
    const CTxMemPoolEntry::relatives& parentIters = it->GetMemPoolParentsConst();
    // add or remove this tx as a child of each parent
    for (const auto& piter : parentIters) {
        UpdateChild(mapTx.iterator_to(piter), it, add);
    }
    const int64_t updateCount = (add ? 1 : -1);
    const int64_t updateSize = updateCount * it->GetTxSize();
    const CAmount updateFee = updateCount * it->GetModifiedFee();
    for (txiter ancestorIt : ancestors) {
        mapTx.modify(ancestorIt, update_descendant_state(updateSize, updateFee, updateCount));
    }
}

void CTxMemPool::UpdateEntryForAncestors(txiter it, const vecEntries &ancestors)
{
    int64_t updateCount = ancestors.size();
    int64_t updateSize = 0;
    CAmount updateFee = 0;
    int64_t updateSigOpsCost = 0;
    for (txiter ancestorIt : ancestors) {
        updateSize += ancestorIt->GetTxSize();
        updateFee += ancestorIt->GetModifiedFee();
        updateSigOpsCost += ancestorIt->GetSigOpCost();
    }
    mapTx.modify(it, update_ancestor_state(updateSize, updateFee, updateCount, updateSigOpsCost));
}

void CTxMemPool::UpdateChildrenForRemoval(txiter it)
{
    const CTxMemPoolEntry::relatives &setMemPoolChildren = it->GetMemPoolChildrenConst();
    for (const auto& updateIt : setMemPoolChildren) {
        UpdateParent(mapTx.iterator_to(updateIt), it, false);
    }
}

void CTxMemPool::UpdateForRemoveFromMempool(const vecEntries &entriesToRemove, bool updateDescendants) {
    // For each entry, walk back all ancestors and decrement size associated with this
    // transaction
    const uint64_t nNoLimit = std::numeric_limits<uint64_t>::max();
    if (updateDescendants) {
        // updateDescendants should be true whenever we're not recursively
        // removing a tx and all its descendants, eg when a transaction is
        // confirmed in a block.
        // Here we only update statistics and not data in mapLinks (which
        // we need to preserve until we're finished with all operations that
        // need to traverse the mempool).
        for (txiter removeIt : entriesToRemove) {
            vecEntries descendants;
            const auto epoch = GetFreshEpoch();
            CalculateDescendantsVec(removeIt, descendants);
            int64_t modifySize = -((int64_t)removeIt->GetTxSize());
            CAmount modifyFee = -removeIt->GetModifiedFee();
            int modifySigOps = -removeIt->GetSigOpCost();
            for (txiter dit : descendants) {
                mapTx.modify(dit, update_ancestor_state(modifySize, modifyFee, -1, modifySigOps));
            }
        }
    }
    for (txiter removeIt : entriesToRemove) {
        vecEntries ancestors;
        const CTxMemPoolEntry &entry = *removeIt;
        std::string dummy;
        // Since this is a tx that is already in the mempool, we can call CMPA
        // with fSearchForParents = false.  If the mempool is in a consistent
        // state, then using true or false should both be correct, though false
        // should be a bit faster.
        // However, if we happen to be in the middle of processing a reorg, then
        // the mempool can be in an inconsistent state.  In this case, the set
        // of ancestors reachable via mapLinks will be the same as the set of
        // ancestors whose packages include this transaction, because when we
        // add a new transaction to the mempool in addUnchecked(), we assume it
        // has no children, and in the case of a reorg where that assumption is
        // false, the in-mempool children aren't linked to the in-block tx's
        // until UpdateTransactionsFromBlock() is called.
        // So if we're being called during a reorg, ie before
        // UpdateTransactionsFromBlock() has been called, then mapLinks[] will
        // differ from the set of mempool parents we'd calculate by searching,
        // and it's important that we use the mapLinks[] notion of ancestor
        // transactions as the set of things to update for removal.
        CalculateMemPoolAncestors(entry, ancestors, nNoLimit, nNoLimit, nNoLimit, nNoLimit, dummy, false);
        // Note that UpdateAncestorsOf severs the child links that point to
        // removeIt in the entries for the parents of removeIt.
        UpdateAncestorsOf(false, removeIt, ancestors);
    }
    // After updating all the ancestor sizes, we can now sever the link between each
    // transaction being removed and any mempool children (ie, update setMemPoolParents
    // for each direct child of a transaction being removed).
    for (txiter removeIt : entriesToRemove) {
        UpdateChildrenForRemoval(removeIt);
    }
}

void CTxMemPoolEntry::UpdateDescendantState(int64_t modifySize, CAmount modifyFee, int64_t modifyCount)
{
    nSizeWithDescendants += modifySize;
    assert(int64_t(nSizeWithDescendants) > 0);
    nModFeesWithDescendants += modifyFee;
    nCountWithDescendants += modifyCount;
    assert(int64_t(nCountWithDescendants) > 0);
}

void CTxMemPoolEntry::UpdateAncestorState(int64_t modifySize, CAmount modifyFee, int64_t modifyCount, int64_t modifySigOps)
{
    nSizeWithAncestors += modifySize;
    assert(int64_t(nSizeWithAncestors) > 0);
    nModFeesWithAncestors += modifyFee;
    nCountWithAncestors += modifyCount;
    assert(int64_t(nCountWithAncestors) > 0);
    nSigOpCostWithAncestors += modifySigOps;
    assert(int(nSigOpCostWithAncestors) >= 0);
}

CTxMemPool::CTxMemPool(CBlockPolicyEstimator* estimator)
    : nTransactionsUpdated(0), minerPolicyEstimator(estimator)
{
    _clear(); //lock free clear

    // Sanity checks off by default for performance, because otherwise
    // accepting transactions becomes O(N^2) where N is the number
    // of transactions in the pool
    nCheckFrequency = 0;
}

bool CTxMemPool::isSpent(const COutPoint& outpoint) const
{
    LOCK(cs);
    const auto& children =  mapNextTx.find(outpoint.hash);
    return children != mapNextTx.end() && children->second.count(outpoint.n);
}

unsigned int CTxMemPool::GetTransactionsUpdated() const
{
    return nTransactionsUpdated;
}

void CTxMemPool::AddTransactionsUpdated(unsigned int n)
{
    nTransactionsUpdated += n;
}

typedef std::unordered_map<uint32_t, const CTxMemPool::txiter, SaltedUInt32Hasher> map_vins;
void CTxMemPool::addUnchecked(const CTxMemPoolEntry &entry, vecEntries &ancestors, bool validFeeEstimate)
{
    NotifyEntryAdded(entry.GetSharedTx());
    // Add to memory pool without checking anything.
    // Used by AcceptToMemoryPool(), which DOES do
    // all the appropriate checks.
    indexed_transaction_set::iterator newit = mapTx.insert(entry).first;

    // Update transaction for any feeDelta created by PrioritiseTransaction
    // TODO: refactor so that the fee delta is calculated before inserting
    // into mapTx.
    CAmount delta{0};
    ApplyDelta(entry.GetTx().GetHash(), delta);
    if (delta) {
            mapTx.modify(newit, update_fee_delta(delta));
    }

    // Update cachedInnerUsage* to include contained transaction's usage.
    // (When we update the entry for in-mempool parents, memory usage will be
    // further updated.)
    cachedInnerUsageEntry += entry.DynamicMemoryUsage();
    cachedInnerUsageParents += memusage::DynamicUsage(entry.GetMemPoolParentsConst());
    cachedInnerUsageChildren += memusage::DynamicUsage(entry.GetMemPoolChildrenConst());

    const CTransaction& tx = newit->GetTx();
    {
        const auto epoch = GetFreshEpoch();
        for (unsigned int i = 0; i < tx.vin.size(); i++) {
            ++cachedInnerMapNextTxSize;
            // TODO: convert to pointer
            // N.B. we try to create with one bucket (as we will use it immediately)
            auto it = mapNextTx.emplace(std::piecewise_construct, std::forward_as_tuple(tx.vin[i].prevout.hash),
                    std::forward_as_tuple(1));
            auto& parents_children = (*it.first).second;
            // only count if we inserted something
            if (it.second) cachedInnerUsageMapNextTx += memusage::DynamicUsage(parents_children);
            // conflicts must already be fully removed
            cachedInnerUsageMapNextTx -= memusage::DynamicUsage(parents_children);
            parents_children.emplace(tx.vin[i].prevout.n, newit);
            cachedInnerUsageMapNextTx += memusage::DynamicUsage(parents_children);
            // Update ancestors with information about this tx
            auto maybe_it = GetIter(tx.vin[i].prevout.hash);
            if (!already_touched(maybe_it)) UpdateParent(newit, *maybe_it, true);
        }
    } // releasing epoch guard is uneccessary but we don't need it past here

    // Don't bother worrying about child transactions of this one.
    // Normal case of a new transaction arriving is that there can't be any
    // children, because such children would be orphans.
    // An exception to that is if a transaction enters that used to be in a block.
    // In that case, our disconnect block logic will call UpdateTransactionsFromBlock
    // to clean up the mess we're leaving here.

    // Update ancestors with information about this tx
    UpdateAncestorsOf(true, newit, ancestors);
    UpdateEntryForAncestors(newit, ancestors);

    nTransactionsUpdated++;
    totalTxSize += entry.GetTxSize();
    if (minerPolicyEstimator) {minerPolicyEstimator->processTransaction(entry, validFeeEstimate);}

    vTxHashes.emplace_back(tx.GetWitnessHash(), newit);
    newit->vTxHashesIdx = vTxHashes.size() - 1;
}

static void resize_if_savings(map_vins& children) {
    // This is still O(N) if resizing while erasing O(N) elements because
    // we'll erase N/2 elements, then rehash for cost of O(N/2)
    // then erase N/4 elements, then rehash for a cost of O(N/4)
    // TODO: batching can be made much more efficient
    assert(children.max_load_factor() == 1);
    // If we're at 0, clear out the map
    if (children.size() == 0) {
        map_vins tmp;
        std::swap(tmp, children);
        return;
    }
    // don't bother saving for small enough sets
    // 19 buckets isn't very large, and fits in with the usual
    // prime rehashing policies
    if (children.bucket_count() <= 19) return;
    // don't bother rehashing if we're more than half full
    const size_t full_size = children.bucket_count();
    if (children.size() > full_size/2) return;

    map_vins tmp{std::make_move_iterator(children.begin()), std::make_move_iterator(children.end()), children.size()};
    std::swap(tmp, children);
}
void CTxMemPool::removeUnchecked(txiter it, MemPoolRemovalReason reason)
{
    NotifyEntryRemoved(it->GetSharedTx(), reason);
    const uint256 hash = it->GetTx().GetHash();
    for (const CTxIn& txin : it->GetTx().vin) {
        auto spends = mapNextTx.find(txin.prevout.hash);
        if (spends == mapNextTx.end()) continue;
        size_t delta = memusage::DynamicUsage(spends->second);
        if (spends->second.erase(txin.prevout.n)) {
            cachedInnerUsageMapNextTx -= delta;
            --cachedInnerMapNextTxSize;
            if (spends->second.empty()) {
                mapNextTx.erase(spends);
            } else{
                resize_if_savings(spends->second);
                cachedInnerUsageMapNextTx += memusage::DynamicUsage(spends->second);
            }
        }
    }

    if (vTxHashes.size() > 1) {
        vTxHashes[it->vTxHashesIdx] = std::move(vTxHashes.back());
        vTxHashes[it->vTxHashesIdx].second->vTxHashesIdx = it->vTxHashesIdx;
        vTxHashes.pop_back();
        if (vTxHashes.size() * 2 < vTxHashes.capacity())
            vTxHashes.shrink_to_fit();
    } else
        vTxHashes.clear();

    totalTxSize -= it->GetTxSize();
    cachedInnerUsageEntry -= it->DynamicMemoryUsage();
    cachedInnerUsageParents -= memusage::DynamicUsage(it->GetMemPoolParentsConst());
    cachedInnerUsageChildren -= memusage::DynamicUsage(it->GetMemPoolChildrenConst());
    mapTx.erase(it);
    nTransactionsUpdated++;
    if (minerPolicyEstimator) {minerPolicyEstimator->removeTx(hash, false);}
}

// Calculates descendants of entry that are not already in descendants, and adds to
// descendants. Assumes entryit is already a tx in the mempool and setMemPoolChildren
// is correct for tx and all descendants.
// Also assumes that if an entry is in descendants already, then all
// in-mempool descendants of it are already in descendants as well, so that we
// can save time by not iterating over those entries.
//
// Note: it does not get inserted into the vector
void CTxMemPool::CalculateDescendantsVec(txiter entryit, vecEntries& descendants) const
{
    // Traverse down the children of entry, only adding children that are not marked as visited by
    // the epoch
    txiter it = entryit;
    size_t idx = descendants.size();
    while (true) {
        for (const auto& pchilditer : it->GetMemPoolChildrenConst()) {
            auto childiter = mapTx.iterator_to(pchilditer);
            if (already_touched(childiter)) continue;
            descendants.push_back(childiter);
        }
        if (idx == descendants.size()) break;
        it = descendants[idx];
        ++idx;
    }
}

void CTxMemPool::removeRecursive(const CTransaction &origTx, MemPoolRemovalReason reason)
{
    // Remove transaction from memory pool
    AssertLockHeld(cs);
    vecEntries txToRemove;
    {
        const auto epoch = GetFreshEpoch();
        txiter origit = mapTx.find(origTx.GetHash());
        // All txToRemove will be touched, this guarantees txToRemove gets no duplicates
        if (origit != mapTx.end()) {
            txToRemove.push_back(origit);
            already_touched(origit);
        } else {
            // When recursively removing but origTx isn't in the mempool
            // be sure to remove any children that are in the pool. This can
            // happen during chain re-orgs if origTx isn't re-accepted into
            // the mempool for any reason.
            auto children = mapNextTx.find(origTx.GetHash());
            // nothing to do, early exit
            if (children == mapNextTx.end()) return;
            for (const auto& child : children->second) {
                if (already_touched(child.second)) continue;
                txToRemove.push_back(child.second);
            }
        }
        // max_idx is used rather than iterator because txToRemove may grow
        const size_t max_idx = txToRemove.size();
        for (size_t idx = 0; idx < max_idx; ++idx) {
            CalculateDescendantsVec(txToRemove[idx], txToRemove);
        }
    } // release epoch guard for RemoveStaged

    RemoveStaged(txToRemove, false, reason);
}

void CTxMemPool::removeForReorg(const CCoinsViewCache *pcoins, unsigned int nMemPoolHeight, int flags)
{
    // Remove transactions spending a coinbase which are now immature and no-longer-final transactions
    AssertLockHeld(cs);
    vecEntries txToRemove;
    // no need for an epoch or a set here since we only visit each it one time.
    for (indexed_transaction_set::const_iterator it = mapTx.begin(); it != mapTx.end(); it++) {
        const CTransaction& tx = it->GetTx();
        LockPoints lp = it->GetLockPoints();
        bool validLP =  TestLockPointValidity(&lp);
        if (!CheckFinalTx(tx, flags) || !CheckSequenceLocks(*this, tx, flags, &lp, validLP)) {
            // Note if CheckSequenceLocks fails the LockPoints may still be invalid
            // So it's critical that we remove the tx and not depend on the LockPoints.
            txToRemove.push_back(it);
        } else if (it->GetSpendsCoinbase()) {
            for (const CTxIn& txin : tx.vin) {
                indexed_transaction_set::const_iterator it2 = mapTx.find(txin.prevout.hash);
                if (it2 != mapTx.end())
                    continue;
                const Coin &coin = pcoins->AccessCoin(txin.prevout);
                if (nCheckFrequency != 0) assert(!coin.IsSpent());
                if (coin.IsSpent() || (coin.IsCoinBase() && ((signed long)nMemPoolHeight) - coin.nHeight < COINBASE_MATURITY)) {
                    txToRemove.push_back(it);
                    break;
                }
            }
        }
        if (!validLP) {
            mapTx.modify(it, update_lock_points(lp));
        }
    }

    {
        const auto epoch = GetFreshEpoch();
        // touch all txToRemove first to force CalculateDescendantsVec
        // to not recurse if we're going to call it later.
        // This guarantees txToRemove gets no duplicates
        for (txiter it : txToRemove) {
            already_touched(it);
        }
        // max_idx is used rather than iterator because txToRemove may grow
        const size_t max_idx = txToRemove.size();
        for (size_t idx = 0; idx < max_idx; ++idx) {
            CalculateDescendantsVec(txToRemove[idx], txToRemove);
        }
    } // release epoch guard for RemoveStaged
    RemoveStaged(txToRemove, false, MemPoolRemovalReason::REORG);

}

void CTxMemPool::removeConflicts(const CTransaction &tx)
{
    // Remove transactions which depend on inputs of tx, recursively
    AssertLockHeld(cs);
    for (const CTxIn &txin : tx.vin) {
        auto children = mapNextTx.find(txin.prevout.hash);
        if (children == mapNextTx.end()) continue;
        auto child = children->second.find(txin.prevout.n);
        if (child == children->second.end()) continue;
        const CTransaction &txConflict = child->second->GetTx();
        if (txConflict != tx)
        {
            ClearPrioritisation(txConflict.GetHash());
            removeRecursive(txConflict, MemPoolRemovalReason::CONFLICT);
        }
    }
}

/**
 * Called when a block is connected. Removes from mempool and updates the miner fee estimator.
 */
void CTxMemPool::removeForBlock(const std::vector<CTransactionRef>& vtx, unsigned int nBlockHeight)
{
    AssertLockHeld(cs);
    std::vector<const CTxMemPoolEntry*> entries;
    for (const auto& tx : vtx)
    {
        uint256 hash = tx->GetHash();

        indexed_transaction_set::iterator i = mapTx.find(hash);
        if (i != mapTx.end())
            entries.push_back(&*i);
    }
    // Before the txs in the new block have been removed from the mempool, update policy estimates
    if (minerPolicyEstimator) {minerPolicyEstimator->processBlock(nBlockHeight, entries);}
    for (const auto& tx : vtx)
    {
        txiter it = mapTx.find(tx->GetHash());
        if (it != mapTx.end()) {
            vecEntries stage{it};
            RemoveStaged(stage, true, MemPoolRemovalReason::BLOCK);
        }
        removeConflicts(*tx);
        ClearPrioritisation(tx->GetHash());
    }
    lastRollingFeeUpdate = GetTime();
    blockSinceLastRollingFeeBump = true;
}

void CTxMemPool::_clear()
{
    mapTx.clear();
    decltype(mapNextTx) tmp;
    std::swap(tmp, mapNextTx);
    totalTxSize = 0;
    cachedInnerUsageEntry = 0;
    cachedInnerUsageParents = 0;
    cachedInnerUsageChildren = 0;
    cachedInnerUsageMapNextTx = 0;
    cachedInnerMapNextTxSize = 0;
    lastRollingFeeUpdate = GetTime();
    blockSinceLastRollingFeeBump = false;
    rollingMinimumFeeRate = 0;
    ++nTransactionsUpdated;
    has_epoch_guard = false;
    m_epoch = 0;
}

void CTxMemPool::clear()
{
    LOCK(cs);
    _clear();
}

static void CheckInputsAndUpdateCoins(const CTransaction& tx, CCoinsViewCache& mempoolDuplicate, const int64_t spendheight)
{
    TxValidationState dummy_state; // Not used. CheckTxInputs() should always pass
    CAmount txfee = 0;
    bool fCheckResult = tx.IsCoinBase() || Consensus::CheckTxInputs(tx, dummy_state, mempoolDuplicate, spendheight, txfee);
    assert(fCheckResult);
    UpdateCoins(tx, mempoolDuplicate, std::numeric_limits<int>::max());
}

void CTxMemPool::check(const CCoinsViewCache *pcoins) const
{
    LOCK(cs);
    if (nCheckFrequency == 0)
        return;

    if (GetRand(std::numeric_limits<uint32_t>::max()) >= nCheckFrequency)
        return;

    LogPrint(BCLog::MEMPOOL, "Checking mempool with %u transactions and %u inputs\n", (unsigned int)mapTx.size(), (unsigned int) cachedInnerMapNextTxSize);

    uint64_t checkTotal = 0;
    uint64_t innerUsageEntry = 0;
    uint64_t innerUsageParents = 0;
    uint64_t innerUsageChildren = 0;
    uint64_t innerUsageMapNextTx = 0;

    CCoinsViewCache mempoolDuplicate(const_cast<CCoinsViewCache*>(pcoins));
    const int64_t spendheight = GetSpendHeight(mempoolDuplicate);

    std::list<const CTxMemPoolEntry*> waitingOnDependants;
    for (indexed_transaction_set::const_iterator it = mapTx.begin(); it != mapTx.end(); it++) {
        unsigned int i = 0;
        checkTotal += it->GetTxSize();
        innerUsageEntry += it->DynamicMemoryUsage();
        const CTransaction& tx = it->GetTx();
        innerUsageParents += memusage::DynamicUsage(it->GetMemPoolParentsConst());
        innerUsageChildren += memusage::DynamicUsage(it->GetMemPoolChildrenConst());
        bool fDependsWait = false;
        {
        const auto epoch = GetFreshEpoch();
        const CTxMemPoolEntry::relatives& parents = it->GetMemPoolParentsConst();
        size_t n_parents_to_check = parents.size();
        for (const CTxIn &txin : tx.vin) {
            // Check that every mempool transaction's inputs refer to available coins, or other mempool tx's.
            indexed_transaction_set::const_iterator it2 = mapTx.find(txin.prevout.hash);
            if (it2 != mapTx.end()) {
                const CTransaction& tx2 = it2->GetTx();
                assert(tx2.vout.size() > txin.prevout.n && !tx2.vout[txin.prevout.n].IsNull());
                fDependsWait = true;
                if (!already_touched(it2)) {
                    assert(parents.count(*it2));
                    --n_parents_to_check;
                }
            } else {
                assert(pcoins->HaveCoin(txin.prevout));
            }
            // Check whether its inputs are marked in mapNextTx.
            auto it3 = mapNextTx.find(txin.prevout.hash);
            assert(it3 != mapNextTx.end());
            assert(it3->first == txin.prevout.hash);
            auto it4 = it3->second.find(txin.prevout.n);
            assert(it4 != it3->second.end());
            assert(it4->first == txin.prevout.n);
            assert(it4->second == it);
            i++;
        }
        // the above asserts imply that every element from tx.vin was in parents
        // the below assert implies that there were exactly parents.size() unique elements
        // which together, imply that the sets are equal
        assert(n_parents_to_check == 0);
        } // release epoch guard

        // Verify ancestor state is correct.
        vecEntries ancestors;
        uint64_t nNoLimit = std::numeric_limits<uint64_t>::max();
        std::string dummy;
        CalculateMemPoolAncestors(*it, ancestors, nNoLimit, nNoLimit, nNoLimit, nNoLimit, dummy);
        uint64_t nCountCheck = ancestors.size() + 1;
        uint64_t nSizeCheck = it->GetTxSize();
        CAmount nFeesCheck = it->GetModifiedFee();
        int64_t nSigOpCheck = it->GetSigOpCost();

        for (txiter ancestorIt : ancestors) {
            nSizeCheck += ancestorIt->GetTxSize();
            nFeesCheck += ancestorIt->GetModifiedFee();
            nSigOpCheck += ancestorIt->GetSigOpCost();
        }

        assert(it->GetCountWithAncestors() == nCountCheck);
        assert(it->GetSizeWithAncestors() == nSizeCheck);
        assert(it->GetSigOpCostWithAncestors() == nSigOpCheck);
        assert(it->GetModFeesWithAncestors() == nFeesCheck);

        // Check children against mapNextTx
        auto mapNextTx_children = mapNextTx.find(it->GetTx().GetHash());
        uint64_t child_sizes = 0;
        if (mapNextTx_children != mapNextTx.end()){
            const auto epoch = GetFreshEpoch();
            const CTxMemPoolEntry::relatives& children = it->GetMemPoolChildrenConst();
            size_t n_children_to_check = children.size();
            for (auto& child : mapNextTx_children->second) {
                txiter childit = mapTx.find(child.second->GetTx().GetHash());
                assert(childit != mapTx.end()); // mapNextTx points to in-mempool transactions
                if (!already_touched(childit)) {
                    child_sizes += childit->GetTxSize();
                    assert(children.count(*childit));
                    --n_children_to_check;
                }
            }
            // the above asserts imply that every element from mapNextTx was in children
            // the below assert implies that there were exactly children.size() unique elements
            // which together, imply that the sets are equal
            assert(n_children_to_check == 0);
        } // release epoch guard

        // Also check to make sure size is greater than sum with immediate children.
        // just a sanity check, not definitive that this calc is correct...
        assert(it->GetSizeWithDescendants() >= child_sizes + it->GetTxSize());

        if (fDependsWait)
            waitingOnDependants.push_back(&(*it));
        else {
            CheckInputsAndUpdateCoins(tx, mempoolDuplicate, spendheight);
        }
    }
    unsigned int stepsSinceLastRemove = 0;
    while (!waitingOnDependants.empty()) {
        const CTxMemPoolEntry* entry = waitingOnDependants.front();
        waitingOnDependants.pop_front();
        if (!mempoolDuplicate.HaveInputs(entry->GetTx())) {
            waitingOnDependants.push_back(entry);
            stepsSinceLastRemove++;
            assert(stepsSinceLastRemove < waitingOnDependants.size());
        } else {
            CheckInputsAndUpdateCoins(entry->GetTx(), mempoolDuplicate, spendheight);
            stepsSinceLastRemove = 0;
        }
    }
    for (auto parent : mapNextTx) {
        innerUsageMapNextTx += memusage::DynamicUsage(parent.second);
        for (auto child : parent.second) {
            uint256 hash = child.second->GetTx().GetHash();
            indexed_transaction_set::const_iterator it2 = mapTx.find(hash);
            assert(it2 != mapTx.end());
            assert(it2 == child.second);
        }
    }

    assert(totalTxSize == checkTotal);
    assert(innerUsageEntry == cachedInnerUsageEntry);
    assert(innerUsageParents == cachedInnerUsageParents);
    assert(innerUsageChildren == cachedInnerUsageChildren);
    assert(innerUsageMapNextTx == cachedInnerUsageMapNextTx);
}

bool CTxMemPool::CompareDepthAndScore(const uint256& hasha, const uint256& hashb)
{
    LOCK(cs);
    indexed_transaction_set::const_iterator i = mapTx.find(hasha);
    if (i == mapTx.end()) return false;
    indexed_transaction_set::const_iterator j = mapTx.find(hashb);
    if (j == mapTx.end()) return true;
    uint64_t counta = i->GetCountWithAncestors();
    uint64_t countb = j->GetCountWithAncestors();
    if (counta == countb) {
        return CompareTxMemPoolEntryByScore()(*i, *j);
    }
    return counta < countb;
}

namespace {
class DepthAndScoreComparator
{
public:
    bool operator()(const CTxMemPool::indexed_transaction_set::const_iterator& a, const CTxMemPool::indexed_transaction_set::const_iterator& b)
    {
        uint64_t counta = a->GetCountWithAncestors();
        uint64_t countb = b->GetCountWithAncestors();
        if (counta == countb) {
            return CompareTxMemPoolEntryByScore()(*a, *b);
        }
        return counta < countb;
    }
};
} // namespace

std::vector<CTxMemPool::indexed_transaction_set::const_iterator> CTxMemPool::GetSortedDepthAndScore() const
{
    std::vector<indexed_transaction_set::const_iterator> iters;
    AssertLockHeld(cs);

    iters.reserve(mapTx.size());

    for (indexed_transaction_set::iterator mi = mapTx.begin(); mi != mapTx.end(); ++mi) {
        iters.push_back(mi);
    }
    std::sort(iters.begin(), iters.end(), DepthAndScoreComparator());
    return iters;
}

void CTxMemPool::queryHashes(std::vector<uint256>& vtxid) const
{
    LOCK(cs);
    auto iters = GetSortedDepthAndScore();

    vtxid.clear();
    vtxid.reserve(mapTx.size());

    for (auto it : iters) {
        vtxid.push_back(it->GetTx().GetHash());
    }
}

static TxMempoolInfo GetInfo(CTxMemPool::indexed_transaction_set::const_iterator it) {
    return TxMempoolInfo{it->GetSharedTx(), it->GetTime(), it->GetFee(), it->GetTxSize(), it->GetModifiedFee() - it->GetFee()};
}

std::vector<TxMempoolInfo> CTxMemPool::infoAll() const
{
    LOCK(cs);
    auto iters = GetSortedDepthAndScore();

    std::vector<TxMempoolInfo> ret;
    ret.reserve(mapTx.size());
    for (auto it : iters) {
        ret.push_back(GetInfo(it));
    }

    return ret;
}

CTransactionRef CTxMemPool::get(const uint256& hash) const
{
    LOCK(cs);
    indexed_transaction_set::const_iterator i = mapTx.find(hash);
    if (i == mapTx.end())
        return nullptr;
    return i->GetSharedTx();
}

TxMempoolInfo CTxMemPool::info(const uint256& hash) const
{
    LOCK(cs);
    indexed_transaction_set::const_iterator i = mapTx.find(hash);
    if (i == mapTx.end())
        return TxMempoolInfo();
    return GetInfo(i);
}

void CTxMemPool::PrioritiseTransaction(const uint256& hash, const CAmount& nFeeDelta)
{
    {
        LOCK(cs);
        CAmount &delta = mapDeltas[hash];
        delta += nFeeDelta;
        txiter it = mapTx.find(hash);
        if (it != mapTx.end()) {
            mapTx.modify(it, update_fee_delta(delta));
            // Now update all ancestors' modified fees with descendants
            vecEntries ancestors;
            uint64_t nNoLimit = std::numeric_limits<uint64_t>::max();
            std::string dummy;
            CalculateMemPoolAncestors(*it, ancestors, nNoLimit, nNoLimit, nNoLimit, nNoLimit, dummy, false);
            for (txiter ancestorIt : ancestors) {
                mapTx.modify(ancestorIt, update_descendant_state(0, nFeeDelta, 0));
            }
            // Now update all descendants' modified fees with ancestors
            vecEntries descendants;
            const auto epoch = GetFreshEpoch();
            CalculateDescendantsVec(it, descendants);
            for (txiter descendantIt : descendants) {
                mapTx.modify(descendantIt, update_ancestor_state(0, nFeeDelta, 0, 0));
            }
            ++nTransactionsUpdated;
        }
    }
    LogPrintf("PrioritiseTransaction: %s feerate += %s\n", hash.ToString(), FormatMoney(nFeeDelta));
}

void CTxMemPool::ApplyDelta(const uint256 hash, CAmount &nFeeDelta) const
{
    LOCK(cs);
    std::map<uint256, CAmount>::const_iterator pos = mapDeltas.find(hash);
    if (pos == mapDeltas.end())
        return;
    const CAmount &delta = pos->second;
    nFeeDelta += delta;
}

void CTxMemPool::ClearPrioritisation(const uint256 hash)
{
    LOCK(cs);
    mapDeltas.erase(hash);
}

const Optional<CTxMemPool::txiter> CTxMemPool::GetConflictTx(const COutPoint& prevout) const
{
    const Optional<txiter> nothing{};
    const auto it = mapNextTx.find(prevout.hash);
    if (it == mapNextTx.end()) return nothing;
    const auto it2 = it->second.find(prevout.n);
    if (it2 == it->second.end()) return nothing;
    return Optional<txiter>{it2->second};
}

Optional<CTxMemPool::txiter> CTxMemPool::GetIter(const uint256& txid) const
{
    auto it = mapTx.find(txid);
    if (it != mapTx.end()) return it;
    return Optional<txiter>{};
}

bool CTxMemPool::HasNoInputsOf(const CTransaction &tx) const
{
    for (unsigned int i = 0; i < tx.vin.size(); i++)
        if (exists(tx.vin[i].prevout.hash))
            return false;
    return true;
}

CCoinsViewMemPool::CCoinsViewMemPool(CCoinsView* baseIn, const CTxMemPool& mempoolIn) : CCoinsViewBacked(baseIn), mempool(mempoolIn) { }

bool CCoinsViewMemPool::GetCoin(const COutPoint &outpoint, Coin &coin) const {
    // If an entry in the mempool exists, always return that one, as it's guaranteed to never
    // conflict with the underlying cache, and it cannot have pruned entries (as it contains full)
    // transactions. First checking the underlying cache risks returning a pruned entry instead.
    CTransactionRef ptx = mempool.get(outpoint.hash);
    if (ptx) {
        if (outpoint.n < ptx->vout.size()) {
            coin = Coin(ptx->vout[outpoint.n], MEMPOOL_HEIGHT, false);
            return true;
        } else {
            return false;
        }
    }
    return base->GetCoin(outpoint, coin);
}

size_t CTxMemPool::DynamicMemoryUsage() const {
    LOCK(cs);
    // Estimate the overhead of mapTx to be 12 pointers + an allocation, as no exact formula for boost::multi_index_contained is implemented.
    return memusage::MallocUsage(sizeof(CTxMemPoolEntry) + 12 * sizeof(void*)) * mapTx.size() + memusage::DynamicUsage(mapNextTx) + memusage::DynamicUsage(mapDeltas) + memusage::DynamicUsage(vTxHashes) + cachedInnerUsageEntry + cachedInnerUsageParents + cachedInnerUsageChildren + cachedInnerUsageMapNextTx;
}

void CTxMemPool::RemoveStaged(vecEntries &stage, bool updateDescendants, MemPoolRemovalReason reason) {
    AssertLockHeld(cs);
    UpdateForRemoveFromMempool(stage, updateDescendants);
    for (txiter it : stage) {
        removeUnchecked(it, reason);
    }
}

int CTxMemPool::Expire(std::chrono::seconds time)
{
    AssertLockHeld(cs);
    indexed_transaction_set::index<entry_time>::type::iterator it = mapTx.get<entry_time>().begin();
    vecEntries tx_to_remove;
    {
        const auto epoch = GetFreshEpoch();
        while (it != mapTx.get<entry_time>().end() && it->GetTime() < time) {
            auto hashed_it = mapTx.project<0>(it);
            if (!already_touched(hashed_it)) tx_to_remove.emplace_back(hashed_it);
            it++;
        }
        for (size_t idx = 0; idx < tx_to_remove.size(); ++idx) {
            CalculateDescendantsVec(tx_to_remove[idx], tx_to_remove);
        }
    } // release epoch guard for RemoveStaged
    RemoveStaged(tx_to_remove, false, MemPoolRemovalReason::EXPIRY);
    return tx_to_remove.size();
}

void CTxMemPool::addUnchecked(const CTxMemPoolEntry &entry, bool validFeeEstimate)
{
    vecEntries ancestors;
    uint64_t nNoLimit = std::numeric_limits<uint64_t>::max();
    std::string dummy;
    CalculateMemPoolAncestors(entry, ancestors, nNoLimit, nNoLimit, nNoLimit, nNoLimit, dummy);
    return addUnchecked(entry, ancestors, validFeeEstimate);
}
static void resize_if_savings(CTxMemPoolEntry::relatives& relatives) {
    // This is still O(N) if resizing while erasing O(N) elements because
    // we'll erase N/2 elements, then rehash for cost of O(N/2)
    // then erase N/4 elements, then rehash for a cost of O(N/4)
    // TODO: batching can be made much more efficient
    assert(relatives.max_load_factor() == 1);
    // If we're at 0, clear out the map
    if (relatives.size() == 0) {
        CTxMemPoolEntry::relatives tmp;
        std::swap(tmp, relatives);
        return;
    }
    // don't bother saving for small enough sets
    // 19 buckets isn't very large, and fits in with the usual
    // prime rehash policies
    if (relatives.bucket_count() <= 19) return;
    // don't bother rehashing if we're more than half full
    const size_t full_size = relatives.bucket_count();
    if (relatives.size() > full_size/2) return;
    // OSX doesn't support make_move_iterator for a reference_wrapper
    CTxMemPoolEntry::relatives tmp{relatives.begin(), relatives.end(), relatives.size()};
    std::swap(tmp, relatives);
}
void CTxMemPool::UpdateChild(txiter entry, txiter child, bool add)
{
    auto& children  = entry->GetMemPoolChildren();
    cachedInnerUsageChildren -= memusage::DynamicUsage(children);
    if (add) children.insert(*child);
    else if (children.erase(*child)) resize_if_savings(children);
    cachedInnerUsageChildren += memusage::DynamicUsage(children);
}

void CTxMemPool::UpdateParent(txiter entry, txiter parent, bool add)
{
    auto& parents  = entry->GetMemPoolParents();
    cachedInnerUsageParents -= memusage::DynamicUsage(parents);
    if (add) parents.insert(*parent);
    else if (parents.erase(*parent)) resize_if_savings(parents);
    cachedInnerUsageParents += memusage::DynamicUsage(parents);
}

CFeeRate CTxMemPool::GetMinFee(size_t sizelimit) const {
    LOCK(cs);
    if (!blockSinceLastRollingFeeBump || rollingMinimumFeeRate == 0)
        return CFeeRate(llround(rollingMinimumFeeRate));

    int64_t time = GetTime();
    if (time > lastRollingFeeUpdate + 10) {
        double halflife = ROLLING_FEE_HALFLIFE;
        if (DynamicMemoryUsage() < sizelimit / 4)
            halflife /= 4;
        else if (DynamicMemoryUsage() < sizelimit / 2)
            halflife /= 2;

        rollingMinimumFeeRate = rollingMinimumFeeRate / pow(2.0, (time - lastRollingFeeUpdate) / halflife);
        lastRollingFeeUpdate = time;

        if (rollingMinimumFeeRate < (double)incrementalRelayFee.GetFeePerK() / 2) {
            rollingMinimumFeeRate = 0;
            return CFeeRate(0);
        }
    }
    return std::max(CFeeRate(llround(rollingMinimumFeeRate)), incrementalRelayFee);
}

void CTxMemPool::trackPackageRemoved(const CFeeRate& rate) {
    AssertLockHeld(cs);
    if (rate.GetFeePerK() > rollingMinimumFeeRate) {
        rollingMinimumFeeRate = rate.GetFeePerK();
        blockSinceLastRollingFeeBump = false;
    }
}

typedef decltype(CTxMemPool().mapNextTx) MapNextTx;
static size_t resize_if_savings(MapNextTx& map_next_tx, size_t allowed_buckets) {
    // This is still O(N) if resizing while erasing O(N) elements because
    // we'll erase N/2 elements, then rehash for cost of O(N/2)
    // then erase N/4 elements, then rehash for a cost of O(N/4)
    // TODO: batching can be made much more efficient
    assert(map_next_tx.max_load_factor() == 1);
    // If we're at 0, clear out the map
    size_t usage = memusage::DynamicUsage(map_next_tx);
    if (map_next_tx.size() == 0) {
        MapNextTx tmp;
        std::swap(tmp, map_next_tx);
        return usage - memusage::DynamicUsage(map_next_tx);
    }
    // don't bother saving for small enough sets
    // 19 buckets isn't very large, and fits in with the usual
    // prime rehashing policies
    if (map_next_tx.bucket_count() <= allowed_buckets) return 0;
    // don't bother rehashing if we're more than half full
    const size_t full_size = map_next_tx.bucket_count();
    if (map_next_tx.size() > full_size/2) return 0;

    MapNextTx tmp{std::make_move_iterator(map_next_tx.begin()), std::make_move_iterator(map_next_tx.end()), map_next_tx.size()};
    std::swap(tmp, map_next_tx);
    return usage - memusage::DynamicUsage(map_next_tx);
}
void CTxMemPool::TrimToSize(size_t sizelimit, std::vector<COutPoint>* pvNoSpendsRemaining) {
    AssertLockHeld(cs);

    unsigned nTxnRemoved = 0;
    CFeeRate maxFeeRateRemoved(0);
    while (!mapTx.empty() && DynamicMemoryUsage() > sizelimit) {
        // recheck if we saved enough space here. Allow at least 1 bucket per entry
        if (resize_if_savings(mapNextTx, mapTx.size())) continue;
        indexed_transaction_set::index<descendant_score>::type::iterator it = mapTx.get<descendant_score>().begin();

        // We set the new mempool min fee to the feerate of the removed set, plus the
        // "minimum reasonable fee rate" (ie some value under which we consider txn
        // to have 0 fee). This way, we don't allow txn to enter mempool with feerate
        // equal to txn which were removed with no block in between.
        CFeeRate removed(it->GetModFeesWithDescendants(), it->GetSizeWithDescendants());
        removed += incrementalRelayFee;
        trackPackageRemoved(removed);
        maxFeeRateRemoved = std::max(maxFeeRateRemoved, removed);

        vecEntries stage;
        {
            const auto epoch = GetFreshEpoch();
            CalculateDescendantsVec(mapTx.project<0>(it), stage);
        } // release epoch guard because RemoveStaged
        stage.push_back(mapTx.project<0>(it));
        nTxnRemoved += stage.size();

        std::vector<CTransaction> txn;
        if (pvNoSpendsRemaining) {
            txn.reserve(stage.size());
            for (txiter iter : stage)
                txn.push_back(iter->GetTx());
        }
        RemoveStaged(stage, false, MemPoolRemovalReason::SIZELIMIT);
        if (pvNoSpendsRemaining) {
            for (const CTransaction& tx : txn) {
                for (const CTxIn& txin : tx.vin) {
                    if (exists(txin.prevout.hash)) continue;
                    pvNoSpendsRemaining->push_back(txin.prevout);
                }
            }
        }
    }

    if (maxFeeRateRemoved > CFeeRate(0)) {
        LogPrint(BCLog::MEMPOOL, "Removed %u txn, rolling minimum fee bumped to %s\n", nTxnRemoved, maxFeeRateRemoved.ToString());
    }
}

// CalculateDescendantMaximum needs to allocate something somewhere for traversal because we can't track state otherwise
// This optimized version re-uses our stack variable in the special case we have exactly one parent.
// If there is exactly one parent going all the way up, this function is cheap / allocation free
// If there is not, we're still agressive about not putting data onto the heap
// We also use recursion where possible to allocate on the stack instead of heap
uint64_t CTxMemPool::CalculateDescendantMaximumInner(std::reference_wrapper<const CTxMemPoolEntry> candidate,
        std::vector<std::reference_wrapper<const CTxMemPoolEntry>>& candidates, uint64_t maximum, uint8_t limit) const {
    bool have_one_to_do = true;
    while (have_one_to_do) {
        have_one_to_do = false;
        const CTxMemPoolEntry::relatives& parents = candidate.get().GetMemPoolParentsConst();
        switch(parents.size()) {
            case 0:
                maximum = std::max(maximum, candidate.get().GetCountWithDescendants());
                break;
            case 1:
                // in the special case where we only have one
                // parent for this entry, we do not need to put
                // it onto the heap or stack
                candidate = *parents.begin();
                // if this one has already been walked we won't increase the maximum
                if (already_touched(mapTx.iterator_to(candidate))) return maximum;
                // We *could* recurse here, but then we are subject to the compiler's
                // choice of TCO. So instead, we re-start the loop
                have_one_to_do = true;
                break;
            default:
                for (const auto& i : parents) {
                    // skip if we've seen it already
                    if (already_touched(mapTx.iterator_to(i))) continue;
                    // first one we find, make it the next one
                    else if (!have_one_to_do) candidate = i;
                    // if we find more than one and can recurse, recurse
                    else if (limit != 0) maximum = CalculateDescendantMaximumInner(i, candidates, maximum, limit-1);
                    // if we find more than one and cannot recurse, queue them
                    else candidates.emplace_back(i);

                    have_one_to_do = true;
                }
                break;
        };
    }
    return maximum;
}
uint64_t CTxMemPool::CalculateDescendantMaximum(txiter entry) const {
    // find parent with highest descendant count
    const auto epoch = GetFreshEpoch();
    std::vector<std::reference_wrapper<const CTxMemPoolEntry>> candidates;
    std::reference_wrapper<const CTxMemPoolEntry> candidate = *entry;
    uint64_t maximum = 0;
    do {
        maximum = CalculateDescendantMaximumInner(candidate, candidates, maximum, 25);
        // Break if nothing left to do
        if (candidates.empty()) return maximum;
        // remove one from heap
        candidate = candidates.back();
        candidates.pop_back();
    } while (true);
}

void CTxMemPool::GetTransactionAncestry(const uint256& txid, size_t& ancestors, size_t& descendants) const {
    LOCK(cs);
    auto it = mapTx.find(txid);
    ancestors = descendants = 0;
    if (it != mapTx.end()) {
        ancestors = it->GetCountWithAncestors();
        descendants = CalculateDescendantMaximum(it);
    }
}

bool CTxMemPool::IsLoaded() const
{
    LOCK(cs);
    return m_is_loaded;
}

void CTxMemPool::SetIsLoaded(bool loaded)
{
    LOCK(cs);
    m_is_loaded = loaded;
}

CTxMemPool::EpochGuard CTxMemPool::GetFreshEpoch() const
{
    return EpochGuard(*this);
}
CTxMemPool::EpochGuard::EpochGuard(const CTxMemPool& in) : pool(in)
{
    assert(!pool.has_epoch_guard);
    ++pool.m_epoch;
    pool.has_epoch_guard = true;
}

CTxMemPool::EpochGuard::~EpochGuard()
{
    // prevents stale results being used
    ++pool.m_epoch;
    pool.has_epoch_guard = false;
}

SaltedTxidHasher::SaltedTxidHasher() : k0(GetRand(std::numeric_limits<uint64_t>::max())), k1(GetRand(std::numeric_limits<uint64_t>::max())) {}
SaltedUInt32Hasher::SaltedUInt32Hasher() : a(GetRand(std::numeric_limits<uint64_t>::max())){}
