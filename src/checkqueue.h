// Copyright (c) 2012-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_CHECKQUEUE_H
#define BITCOIN_CHECKQUEUE_H

#include <algorithm>
#include <vector>
#include <thread>
#include <mutex>
#include <condition_variable>

template <typename T>
class CCheckQueueControl;

/**
 * Queue for verifications that have to be performed.
  * The verifications are represented by a type T, which must provide an
  * operator(), returning a bool.
  *
  * One thread (the master) is assumed to push batches of verifications
  * onto the queue, where they are processed by N-1 worker threads. When
  * the master is done adding work, it temporarily joins the worker pool
  * as an N'th worker, until all jobs are done.
  */
template <typename T>
class CCheckQueue
{
private:
    //! Mutex to ensure that sleeping threads are woken.
    std::mutex mutex;

    //! Worker threads block on this when out of work
    std::condition_variable condWorker;

    //! The temporary evaluation result.
    std::atomic_flag fAllOk;

    //! Container for worker threads
    std::vector<std::thread> threads;
    /**
     * Number of verification threads that aren't in stand-by. When a thread is
     * awake it may have a job that will return false, but is yet to report the
     * result through fAllOk.
     */
    std::atomic<unsigned int> nAwake;


    //! Whether we're shutting down.
    bool fQuit;

    //! The maximum number of elements to be processed in one batch
    unsigned int nBatchSize;

    //! A pointer to contiguous memory that contains all checks
    T* check_mem {nullptr};

    /** The begin and end offsets into check_mem. 128 bytes of padding is
     * inserted before and after check_mem_top to eliminate false sharing*/
    std::atomic<uint32_t> check_mem_bot {0};
    unsigned char _padding[128];
    /** check_mem_top stores the upper offset. The msb of check_mem_top stores
     * if the last check has been added in a given round, which is also used to
     * detect if there is presently a master process either in the queue or
     * adding jobs.
     */
    std::atomic<uint32_t> check_mem_top {0};
    unsigned char _padding2[128];

    /** Internal function that does bulk of the verification work. */
    bool Loop(bool fMaster = false)
    {

        // first iteration, only count non-master threads
        if (!fMaster) ++nAwake;
        uint32_t top_cache = fMaster ? check_mem_top.load(std::memory_order_relaxed) & ~(1u<<31) : 0;
        bool final_check_added = fMaster;
        for (;;) {
            uint32_t bottom_cache = check_mem_bot.load(std::memory_order_relaxed);
            // Try to increment bottom_cache by 1 if our version of bottom_cache
            // indicates that there is work to be done.
            // E.g., if bottom_cache = top_cache, don't attempt to exchange.
            //       if  bottom_cache < top_cache, then do attempt to exchange
            //
            // compare_exchange_weak, on failure, updates bottom_cache to latest
            while (top_cache > bottom_cache &&
                    !check_mem_bot.compare_exchange_weak( bottom_cache, bottom_cache+1, std::memory_order_relaxed));
            if (top_cache > bottom_cache) {
                // ^^ If we have work to do execute work.
                // We compute using bottom_cache (not bottom_cache + 1 as
                // above) because it is 0-indexed
                if (!(*(check_mem + bottom_cache))()) {
                    // Fast Exit
                    // Heuristic that this will set check_mem_bot appropriately so that workers aren't spinning for a long time.
                    check_mem_bot.store(std::numeric_limits<uint32_t>::max(), std::memory_order_relaxed);
                    fAllOk.clear(std::memory_order_relaxed);
                }
                continue;
            }
            if (fMaster) {
                check_mem_top.store(1u<<31, std::memory_order_relaxed);
                // There's no harm to the master holding the lock
                // at this point because all the jobs are taken.
                // so busy spin until no one else is awake
                while (nAwake.load(std::memory_order_acquire)) {}
                return fAllOk.test_and_set(std::memory_order_release);
            }
            if (!final_check_added) {
                top_cache = check_mem_top.load(std::memory_order_acquire);
                final_check_added = top_cache >> 31;
                top_cache &= ~(1u<<31);
                // if this is our first time observing that the final check was
                // added, skip back to the top to complete all work
                if (final_check_added) continue;
            }
            if (final_check_added) {
                // ^^ Read once outside the lock and once inside
                nAwake.fetch_sub(1, std::memory_order_release); //  Release all writes to fAllOk before sleeping!
                // Unfortunately we need this lock for this to be safe
                // We hold it for the min time possible
                {
                    std::unique_lock<std::mutex> lock(mutex);
                    // Technically this won't wake up if a master thread joins
                    // and leaves very quickly without adding jobs, before the
                    // notify is processed, but that's OK.
                    condWorker.wait(lock, [&]{ return fQuit || check_mem_top.load(std::memory_order_relaxed) != (1u<<31);});
                    if (fQuit)
                        return false;
                }
                nAwake.fetch_add(1, std::memory_order_release);
                top_cache = check_mem_top.load(std::memory_order_acquire);
                final_check_added = top_cache >> 31;
                top_cache &= ~(1u<<31);
                continue;
            }
        }
    }


public:
    //! Mutex to ensure only one concurrent CCheckQueueControl
    std::mutex ControlMutex;

    //! Create a new check queue
    CCheckQueue(unsigned int nBatchSizeIn) :  fAllOk(), nAwake(0), fQuit(false), nBatchSize(nBatchSizeIn), check_mem(nullptr), check_mem_bot(0), check_mem_top(1u<<31)
    {
        fAllOk.test_and_set();
    }

    //! Worker thread
    void Thread()
    {
        threads.emplace_back(&CCheckQueue::Loop, this, false);
    }

    //! Wait until execution finishes, and return whether all evaluations were successful.
    bool Wait()
    {
        DoneAdding();
        return Loop(true);
    }

    //! Setup is called once per batch to point the CheckQueue to the
    // checks & restart the counters.
    void Setup(T* check_mem_in)
    {
        {
            std::lock_guard<std::mutex> lock(mutex);
            check_mem = check_mem_in;
            check_mem_top.store(0, std::memory_order_relaxed);
            check_mem_bot.store(0, std::memory_order_relaxed);
        }
        condWorker.notify_all();
    }

    //! Add a batch of checks to the queue
    void Add(size_t size)
    {
        check_mem_top.fetch_add(size, std::memory_order_release);
    }

    //! Signal that no more checks will be added
    void DoneAdding()
    {
        check_mem_top.fetch_or(1u<<31, std::memory_order_relaxed);
    }

    void Interrupt()
    {
        {
            while (nAwake.load());
            std::lock_guard<std::mutex> control_lock(ControlMutex);
            std::lock_guard<std::mutex> notify_lock(mutex);
            fQuit = true;
            check_mem_top = (1u<<31);
        }
        condWorker.notify_all();
    }

    void Stop()
    {
        for (auto& t: threads)
            t.join();
        threads.clear();
    }

    ~CCheckQueue()
    {
        Interrupt();
        Stop();
    }

};

/**
 * RAII-style controller object for a CCheckQueue that guarantees the passed
 * queue is finished before continuing.
 */
template <typename T>
class CCheckQueueControl
{
private:
    std::vector<T> check_mem;
    CCheckQueue<T>* pqueue;
    bool fDone;

public:
    CCheckQueueControl() = delete;
    CCheckQueueControl(const CCheckQueueControl&) = delete;
    CCheckQueueControl& operator=(const CCheckQueueControl&) = delete;
    explicit CCheckQueueControl(CCheckQueue<T> * const pqueueIn, const unsigned int size) : check_mem(), pqueue(pqueueIn), fDone(false)
    {
        // passed queue is supposed to be unused, or NULL
        if (pqueue != NULL) {
            ENTER_CRITICAL_SECTION(pqueue->ControlMutex);
            check_mem.reserve(size);
            pqueue->Setup(check_mem.data());
        }
    }

    bool Wait()
    {
        if (pqueue == NULL)
            return true;
        bool fRet = pqueue->Wait();
        fDone = true;
        return fRet;
    }

    //! Deprecated. emplacement Add + Flush are the preferred method for adding
    // checks to the queue.
    void Add(std::vector<T>& vChecks)
    {
        if (pqueue != NULL) {
            auto s = vChecks.size();
            for (T& x : vChecks) {
                check_mem.emplace_back();
                check_mem.back().swap(x);
            }
            pqueue->Add(s);
        }
    }

    //! Add directly constructs a check on the Controller's memory
    // Checks created via emplacement Add won't be executed
    // until a subsequent Flush call.
    template<typename ... Args>
    void Add(Args && ... args)
    {
        if (pqueue != NULL) {
            check_mem.emplace_back(std::forward<Args>(args)...);
        }
    }

    //! FLush is called to inform the worker of new jobs
    void Flush(size_t s)
    {
        if (pqueue != NULL) {
            pqueue->Add(s);
        }
    }

    ~CCheckQueueControl()
    {
        if (!fDone)
            Wait();
        if (pqueue != NULL) {
            LEAVE_CRITICAL_SECTION(pqueue->ControlMutex);
        }
    }
};

#endif // BITCOIN_CHECKQUEUE_H
