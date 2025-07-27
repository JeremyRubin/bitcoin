// Copyright (c) 2017-2022 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <index/txindex.h>

#include <clientversion.h>
#include <common/args.h>
#include <evmc/evmc.h>
#include <evmone/evmone.h>
#include <index/disktxpos.h>
#include <logging.h>
#include <node/blockstorage.h>
#include <validation.h>

constexpr uint8_t DB_TXINDEX{'t'};

std::unique_ptr<TxIndex> g_txindex;


class EvmoneVM
{
public:
    EvmoneVM() : m_vm{(evmc_create_evmone())} {}
    ~EvmoneVM()
    {
        if (m_vm) {
            m_vm.get()->destroy(m_vm.get());
        }
    }

    void Execute(std::vector<unsigned char>& input, int64_t& gas_in_out)
    {
        if (m_vm == nullptr) {
            return;
        }
        /* @param vm         The VM instance. This argument MUST NOT be NULL.
         * @param host       The Host interface. This argument MUST NOT be NULL unless
         *                   the @p vm has the ::EVMC_CAPABILITY_PRECOMPILES capability.
         * @param context    The opaque pointer to the Host execution context.
         *                   This argument MAY be NULL. The VM MUST pass the same
         *                   pointer to the methods of the @p host interface.
         *                   The VM MUST NOT dereference the pointer.
         * @param rev        The requested EVM specification revision.
         * @param msg        The call parameters. See ::evmc_message. This argument MUST NOT be NULL.
         * @param code       The reference to the code to be executed. This argument MAY be NULL.
         * @param code_size  The length of the code. If @p code is NULL this argument MUST be 0.
         * @return           The execution result.
         */
        auto host = nullptr;
        auto context = nullptr;
        auto rev = EVMC_CANCUN;


        auto kind = EVMC_CALL; // Assuming we are executing a call
        uint32_t flags = 0;
        DataStream input_stream{input};
        input_stream >> flags; // Read flags from input
                               //
        auto depth = 0;
        int64_t gas = gas_in_out;
        evmc_address recipient;
        evmc_address sender;
        input_stream >> recipient.bytes; // Read recipient address
        input_stream >> sender.bytes;    // Read sender address


        std::vector<unsigned char> input_data;
        input_stream >> input_data; // Read input data
        size_t input_size = input_data.size();

        evmc_bytes32 value{};
        input_stream >> value.bytes; // Read value, if applicable

        evmc_bytes32 salt{};
        input_stream >> salt.bytes; // Read salt, if applicable

        evmc_address code_address;
        input_stream >> code_address.bytes; // Read code address, if applicable

        std::vector<unsigned char> code;
        input_stream >> code; // Read code, if applicable
        size_t code_size = code.size();
        evmc_message msg{kind, flags,
                         depth, gas, recipient, sender,
                         input_data.data(), input_size, value,
                         salt, code_address, code.data(), code_size};


        auto code_dummy = nullptr; // Assuming we don't have code to execute, just input data.
        auto code_size_dummy = 0;
        auto result = m_vm.get()->execute(m_vm.get(), host, context, rev, &msg, code_dummy, code_size_dummy);
        if (result.release) {
            result.release(&result);
        }
    }

    evmc_vm* get() { return m_vm.get(); }

private:
    std::unique_ptr<evmc_vm> m_vm;
};


static int64_t FeeToGas(CAmount fee)
{
    // Assuming a fixed gas price for simplicity, this can be adjusted based on network conditions.
    const CAmount gas_per_sat = 1000; // Example gas price in satoshis
    return fee * gas_per_sat;
}

/** Access to the txindex database (indexes/txindex/) */
class TxIndex::DB : public BaseIndex::DB
{
    EvmoneVM m_evmone_vm; // EVM support, if needed
public:
    bool RunEVM(const CTransactionRef& tx, TxIndex& txindex)
    {
        std::vector<std::vector<unsigned char>> annexes;
        if (m_evmone_vm.get() == nullptr) return false;
        CAmount total = 0;
        for (const auto& input : tx->vin) {
            if (!input.scriptSig.empty()) continue; // Skip empty scripts
            CTransactionRef ref;
            uint256 blockhash;
            txindex.FindTx(input.prevout.hash, blockhash, ref);
            std::vector<unsigned char> witnessprogram;
            int witnessversion = 0;
            if (!ref->vout[input.prevout.n].scriptPubKey.IsWitnessProgram(witnessversion, witnessprogram)) continue;
            total += ref->vout[input.prevout.n].nValue;

            if (!(witnessversion == 1 && witnessprogram.size() == WITNESS_V1_TAPROOT_SIZE)) continue;


            const auto& stack = input.scriptWitness.stack;
            if (stack.size() >= 2 && !stack.back().empty() && stack.back()[0] == ANNEX_TAG) {
                // Skip ANNEX tag
                std::vector<unsigned char> annex = stack.back();
                annexes.push_back(annex);
            }
        }

        for (const auto& output : tx->vout) {
            total -= output.nValue;
        }

        int64_t gas_in_out = FeeToGas(total); // Assuming gas is passed in and out

        for (auto& annex : annexes) {
            if (annex.empty()) continue; // Skip empty annexes
            m_evmone_vm.Execute(annex, gas_in_out);
        }
        return true;
    }

    explicit DB(size_t n_cache_size, bool f_memory = false, bool f_wipe = false);

    /// Read the disk location of the transaction data with the given hash. Returns false if the
    /// transaction hash is not indexed.
    bool ReadTxPos(const uint256& txid, CDiskTxPos& pos) const;

    /// Write a batch of transaction positions to the DB.
    [[nodiscard]] bool WriteTxs(const std::vector<std::pair<uint256, CDiskTxPos>>& v_pos);
};

TxIndex::DB::DB(size_t n_cache_size, bool f_memory, bool f_wipe) : BaseIndex::DB(gArgs.GetDataDirNet() / "indexes" / "txindex", n_cache_size, f_memory, f_wipe)
{
}

bool TxIndex::DB::ReadTxPos(const uint256& txid, CDiskTxPos& pos) const
{
    return Read(std::make_pair(DB_TXINDEX, txid), pos);
}

bool TxIndex::DB::WriteTxs(const std::vector<std::pair<uint256, CDiskTxPos>>& v_pos)
{
    CDBBatch batch(*this);
    for (const auto& tuple : v_pos) {
        batch.Write(std::make_pair(DB_TXINDEX, tuple.first), tuple.second);
    }
    return WriteBatch(batch);
}

TxIndex::TxIndex(std::unique_ptr<interfaces::Chain> chain, size_t n_cache_size, bool f_memory, bool f_wipe)
    : BaseIndex(std::move(chain), "txindex"), m_db(std::make_unique<TxIndex::DB>(n_cache_size, f_memory, f_wipe))
{
}

TxIndex::~TxIndex() = default;

bool TxIndex::CustomAppend(const interfaces::BlockInfo& block)
{
    // Exclude genesis block transaction because outputs are not spendable.
    if (block.height == 0) return true;

    assert(block.data);
    CDiskTxPos pos({block.file_number, block.data_pos}, GetSizeOfCompactSize(block.data->vtx.size()));
    std::vector<std::pair<uint256, CDiskTxPos>> vPos;
    vPos.reserve(block.data->vtx.size());
    for (const auto& tx : block.data->vtx) {
        vPos.emplace_back(tx->GetHash(), pos);
        pos.nTxOffset += ::GetSerializeSize(TX_WITH_WITNESS(*tx));
    }
    bool b = m_db->WriteTxs(vPos);

    for (const auto& tx : block.data->vtx) {
        m_db->RunEVM(tx, *this); // Run EVM on each transaction
    }


    return b;
}

BaseIndex::DB& TxIndex::GetDB() const { return *m_db; }

bool TxIndex::FindTx(const uint256& tx_hash, uint256& block_hash, CTransactionRef& tx) const
{
    CDiskTxPos postx;
    if (!m_db->ReadTxPos(tx_hash, postx)) {
        return false;
    }

    AutoFile file{m_chainstate->m_blockman.OpenBlockFile(postx, true)};
    if (file.IsNull()) {
        LogError("OpenBlockFile failed");
        return false;
    }
    CBlockHeader header;
    try {
        file >> header;
        file.seek(postx.nTxOffset, SEEK_CUR);
        file >> TX_WITH_WITNESS(tx);
    } catch (const std::exception& e) {
        LogError("Deserialize or I/O error - %s", e.what());
        return false;
    }
    if (tx->GetHash() != tx_hash) {
        LogError("txid mismatch");
        return false;
    }
    block_hash = header.GetHash();
    return true;
}
