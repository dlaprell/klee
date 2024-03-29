//===-- ExecutionState.h ----------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_EXECUTIONSTATE_H
#define KLEE_EXECUTIONSTATE_H

#include "klee/Constraints.h"
#include "klee/Expr.h"
#include "klee/Internal/ADT/TreeStream.h"
#include "klee/MergeHandler.h"
#include "klee/Thread.h"

// FIXME: We do not want to be exposing these? :(
#include "../../lib/Core/AddressSpace.h"
#include "klee/Internal/Module/KInstIterator.h"

#include <map>
#include <set>
#include <vector>

namespace klee {
class Array;
class CallPathNode;
struct Cell;
struct KFunction;
struct KInstruction;
class MemoryObject;
class PTreeNode;
struct InstructionInfo;
class MemoryAccessTracker;
class Executor;

llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const MemoryMap &mm);

/// @brief ExecutionState representing a path under exploration
class ExecutionState {
  friend class Executor;

public:
  typedef std::vector<StackFrame> stack_ty;
  typedef std::map<Thread::ThreadId, Thread> threads_ty;

  typedef uint8_t ScheduleReason;
  static const ScheduleReason MEMORY_ACCESS = 1;
  static const ScheduleReason THREAD_CREATION = 2;
  static const ScheduleReason THREAD_WAKEUP = 4;
  static const ScheduleReason PREDECESSOR = 8;

  struct ScheduleDependency {
    uint64_t scheduleIndex;
    Thread::ThreadId tid;
    ScheduleReason reason;

    ScheduleDependency() = default;
    ScheduleDependency(const ScheduleDependency &d) = default;
  };

  struct EpochDependencies {
    uint64_t hash = 0;
    std::vector<ScheduleDependency> dependencies;

    EpochDependencies() = default;
    EpochDependencies(const EpochDependencies &d) = default;
  };

  struct ScheduleEpoch {
    Thread::ThreadId tid;
    uint64_t dependencyHash;
  };

private:
  // unsupported, use copy constructor
  ExecutionState &operator=(const ExecutionState &);

  std::map<std::string, std::string> fnAliases;

  /// @brief Pointer to the thread that is currently executed
  threads_ty::iterator currentThreadIterator;

  /// @brief The sync point where we wait for the threads
  uint64_t currentSchedulingIndex;

  bool onlyOneThreadRunnableSinceEpochStart;

  std::map<Thread::ThreadId, ScheduleDependency> forwardDeclaredDependencies;

  /// @brief the tracker that will keep all memory access
  // This is a little bit of a hack: we do not want to expose the tracker to the 'public' api so
  // we use a pointer here even if the tracker is 'owned' by this state
  MemoryAccessTracker* memAccessTracker;

public:
  // Execution - Control Flow specific

  uint64_t completedScheduleCount;

  /// @brief Thread map representing all threads that exist at the moment
  threads_ty threads;

    /// @brief the history of scheduling up until now
  std::vector<ScheduleEpoch> schedulingHistory;

  /// @brief set of all threads that could in theory be executed
  std::set<Thread::ThreadId> runnableThreads;

  /// @brief if thread scheduling is enabled at the current time
  bool threadSchedulingEnabled;

  // Thread scheduling specific state data

  std::map<Thread::ThreadId, std::vector<EpochDependencies>> scheduleDependencies;

  // Overall state of the state - Data specific

  /// @brief Address space used by this state (e.g. Global and Heap)
  AddressSpace addressSpace;

  /// @brief Constraints collected so far
  ConstraintManager constraints;

  /// Statistics and information

  /// @brief Costs for all queries issued for this state, in seconds
  mutable double queryCost;

  /// @brief Weight assigned for importance of this state.  Can be
  /// used for searchers to decide what paths to explore
  double weight;

  /// @brief Exploration depth, i.e., number of times KLEE branched for this state
  unsigned depth;

  /// @brief History of complete path: represents branches taken to
  /// reach/create this state (both concrete and symbolic)
  TreeOStream pathOS;

  /// @brief History of symbolic path: represents symbolic branches
  /// taken to reach/create this state
  TreeOStream symPathOS;

  /// @brief Counts how many instructions were executed since the last new
  /// instruction was covered.
  unsigned instsSinceCovNew;

  /// @brief Whether a new instruction was covered in this state
  bool coveredNew;

  /// @brief Disables forking for this state. Set by user code
  bool forkDisabled;

  /// @brief Set containing which lines in which files are covered by this state
  std::map<const std::string *, std::set<unsigned> > coveredLines;

  /// @brief Pointer to the process tree of the current state
  PTreeNode *ptreeNode;

  /// @brief Ordered list of symbolics: used to generate test cases.
  //
  // FIXME: Move to a shared list structure (not critical).
  std::vector<std::pair<const MemoryObject *, const Array *> > symbolics;

  /// @brief Set of used array names for this state.  Used to avoid collisions.
  std::set<std::string> arrayNames;

  std::string getFnAlias(std::string fn);
  void addFnAlias(std::string old_fn, std::string new_fn);
  void removeFnAlias(std::string fn);

  // The objects handling the klee_open_merge calls this state ran through
  std::vector<ref<MergeHandler> > openMergeStack;

  // The numbers of times this state has run through Executor::stepInstruction
  std::uint64_t steppedInstructions;

private:
  ExecutionState() : ptreeNode(0) {}

  std::vector<const MemoryObject *> popFrameOfThread(Thread* thread);

  bool hasSameThreadState(const ExecutionState &b, Thread::ThreadId tid);

  void dumpStackOfThread(llvm::raw_ostream &out, const Thread* thread) const;

  void assembleDependencyIndicator();

public:
  ExecutionState(KFunction *kf);

  // XXX total hack, just used to make a state so solver can
  // use on structure
  ExecutionState(const std::vector<ref<Expr> > &assumptions);

  ExecutionState(const ExecutionState &state);

  ~ExecutionState();

  ExecutionState *branch();

  /// @brief returns the reference to the current thread (only valid for one 'klee instruction')
  Thread* getCurrentThreadReference() const;

    /// @brief returns the reference to the thread with the given tid (only valid for one 'klee instruction')
  Thread* getThreadReferenceById(Thread::ThreadId tid);

  EpochDependencies* getCurrentEpochDependencies();

  void endCurrentEpoch();

  void trackScheduleDependency(ScheduleDependency dep);

  void trackScheduleDependency(uint64_t scheduleIndex, Thread::ThreadId tid, ScheduleReason r);

  // The method below is a bit 'unstable' with regards to the thread id
  // -> probably at a later state the thread id will be created by the ExecutionState
  /// @brief will create a new thread with the given thread id
  Thread* createThread(KFunction *kf, ref<Expr> arg);

  //// @brief will put the current thread into sleep mode
  void sleepCurrentThread();

  /// @brief wakes a specific thread up
  void wakeUpThread(Thread::ThreadId tid);

  /// @brief will preempt the current thread for the current sync phase
  void preemptThread(Thread::ThreadId tid);

  /// @brief will exit the referenced thread
  void exitThread(Thread::ThreadId tid);

  /// @brief update the current scheduled thread
  void scheduleNextThread(Thread::ThreadId tid);

  void trackMemoryAccess(const MemoryObject* mo, ref<Expr> offset, uint8_t type);

  std::vector<const MemoryObject *> popFrameOfCurrentThread();

  void addSymbolic(const MemoryObject *mo, const Array *array);
  void addConstraint(ref<Expr> e) { constraints.addConstraint(e); }

  bool merge(const ExecutionState &b);
  void dumpStack(llvm::raw_ostream &out) const;
  void dumpSchedulingInfo(llvm::raw_ostream &out) const;
  void dumpAllThreadStacks(llvm::raw_ostream &out) const;
};
}

#endif
