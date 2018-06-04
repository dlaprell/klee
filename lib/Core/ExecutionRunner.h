#ifndef KLEE_EXECUTIONRUNNER_H
#define KLEE_EXECUTIONRUNNER_H

#include "Executor.h"

namespace klee {
  class ExecutionRunner {
    friend class Executor;

    private:
      Searcher *searcher;
      PTree *processTree;
      TimingSolver *solver;
      Executor* executor;
      SpecialFunctionHandler* specialFunctionHandler;

      std::set<ExecutionState*> states;

      /// Used to track states that have been added during the current
      /// instructions step.
      /// \invariant \ref addedStates is a subset of \ref states.
      /// \invariant \ref addedStates and \ref removedStates are disjoint.
      std::vector<ExecutionState *> addedStates;
      /// Used to track states that have been removed during the current
      /// instructions step.
      /// \invariant \ref removedStates is a subset of \ref states.
      /// \invariant \ref addedStates and \ref removedStates are disjoint.
      std::vector<ExecutionState *> removedStates;

      /// Used to track states that are not terminated, but should not
      /// be scheduled by the searcher.
      std::vector<ExecutionState *> pausedStates;
      /// States that were 'paused' from scheduling, that now may be
      /// scheduled again
      std::vector<ExecutionState *> continuedStates;

    public:
      explicit ExecutionRunner(Executor* exec);
      void stepInState(ExecutionState& state);

    private:
      Cell& getArgumentCell(ExecutionState &state,
                            KFunction *kf,
                            unsigned index) {
        // FIXME: Just assume that we the call should return the current thread, but what is the correct behavior
        Thread* thread = state.getCurrentThreadReference();
        return thread->stack.back().locals[kf->getArgRegister(index)];
      }

      Cell& getDestCell(ExecutionState &state,
                        KInstruction *target) {
        // FIXME: Just assume that we the call should return the current thread, but what is the correct behavior
        Thread* thread = state.getCurrentThreadReference();
        return thread->stack.back().locals[target->dest];
      }

      const Cell& eval(KInstruction *ki, unsigned index, ExecutionState &state) const;
      void bindLocal(KInstruction *target, ExecutionState &state, ref<Expr> value);
      void bindArgument(KFunction *kf, unsigned index, ExecutionState &state, ref<Expr> value);
      ref<Expr> toUnique(const ExecutionState &state, ref<Expr> &e);
      ref<klee::ConstantExpr> toConstant(ExecutionState &state, ref<Expr> e, const char *reason);
      void addConstraint(ExecutionState &state, ref<Expr> condition);

      void transferToBasicBlock(llvm::BasicBlock *dst, llvm::BasicBlock *src, ExecutionState &state);
      llvm::Function* getTargetFunction(llvm::Value *calledVal, ExecutionState &state);

      void executeCall(ExecutionState &state,
                       KInstruction *ki,
                       llvm::Function *f,
                       std::vector< ref<Expr> > &arguments);

      ObjectState *bindObjectInState(ExecutionState &state, const MemoryObject *mo,
                                     bool isLocal, const Array *array = nullptr);

      // do address resolution / object binding / out of bounds checking
      // and perform the operation
      void executeMemoryOperation(ExecutionState &state,
                                  bool isWrite,
                                  ref<Expr> address,
                                  ref<Expr> value /* undef if read */,
                                  KInstruction *target /* undef if write */);

      void stepInstruction(ExecutionState &state);
      void executeInstruction(ExecutionState &state, KInstruction *ki);

      void callExternalFunction(ExecutionState &state,
                                KInstruction *target,
                                llvm::Function *function,
                                std::vector< ref<Expr> > &arguments);

      /// Bind a constant value for e to the given target. NOTE: This
      /// function may fork state if the state has multiple seeds.
      void executeGetValue(ExecutionState &state, ref<Expr> e, KInstruction *target);

      size_t getAllocationAlignment(const llvm::Value *allocSite) const;

      void resolveExact(ExecutionState &state,
                        ref<Expr> p,
                        Executor::ExactResolutionList &results,
                        const std::string &name);

      /// Get textual information regarding a memory address.
      std::string getAddressInfo(ExecutionState &state, ref<Expr> address) const;

      /// Allocate and bind a new object in a particular state. NOTE: This
      /// function may fork.
      ///
      /// \param isLocal Flag to indicate if the object should be
      /// automatically deallocated on function return (this also makes it
      /// illegal to free directly).
      ///
      /// \param target Value at which to bind the base address of the new
      /// object.
      ///
      /// \param reallocFrom If non-zero and the allocation succeeds,
      /// initialize the new object from the given one and unbind it when
      /// done (realloc semantics). The initialized bytes will be the
      /// minimum of the size of the old and new objects, with remaining
      /// bytes initialized as specified by zeroMemory.
      void executeAlloc(ExecutionState &state,
                        ref<Expr> size,
                        bool isLocal,
                        KInstruction *target,
                        bool zeroMemory=false,
                        const ObjectState *reallocFrom = nullptr);

      /// Free the given address with checking for errors. If target is
      /// given it will be bound to 0 in the resulting states (this is a
      /// convenience for realloc). Note that this function can cause the
      /// state to fork and that \ref state cannot be safely accessed
      /// afterwards.
      void executeFree(ExecutionState &state,
                       ref<Expr> address,
                       KInstruction *target = nullptr);

      /// Create a new state where each input condition has been added as
      /// a constraint and return the results. The input state is included
      /// as one of the results. Note that the output vector may included
      /// NULL pointers for states which were unable to be created.
      void branch(ExecutionState &state,
                  const std::vector< ref<Expr> > &conditions,
                  std::vector<ExecutionState*> &result);

      // Fork current and return states in which condition holds / does
      // not hold, respectively. One of the states is necessarily the
      // current state, and one of the states may be null.
      Executor::StatePair fork(ExecutionState &current, ref<Expr> condition, bool isInternal);

      void executeMakeSymbolic(ExecutionState &state, const MemoryObject *mo,
                               const std::string &name);

      KFunction* obtainFunctionFromExpression(ref<Expr> address);

      void exitWithDeadlock(ExecutionState &state);

      void exitWithUnsafeMemAccess(ExecutionState &state,
                                   const MemoryObject* mo);

      bool processMemoryAccess(ExecutionState &state, const MemoryObject* mo,
                               ref<Expr> offset, uint8_t type);

      void createThread(ExecutionState &state, Thread::ThreadId tid, ref<Expr> startRoutine, ref<Expr> arg);
      void sleepThread(ExecutionState &state);
      void wakeUpThread(ExecutionState &state, Thread::ThreadId tid);
      void preemptThread(ExecutionState &state);
      void exitThread(ExecutionState &state);
      void toggleThreadScheduling(ExecutionState &state, bool enabled);

      void scheduleThreads(ExecutionState &state);

      // remove state from queue and delete
      void terminateState(ExecutionState &state);
      // call exit handler and terminate state
      void terminateStateEarly(ExecutionState &state, const llvm::Twine &message);
      // call exit handler and terminate state
      void terminateStateOnExit(ExecutionState &state);
      // call error handler and terminate state
      void terminateStateOnError(ExecutionState &state, const llvm::Twine &message,
                                 enum Executor::TerminateReason termReason,
                                 const char *suffix = NULL,
                                 const llvm::Twine &longMessage = "");

      // call error handler and terminate state, for execution errors
      // (things that should not be possible, like illegal instruction or
      // unlowered instrinsic, or are unsupported, like inline assembly)
      void terminateStateOnExecError(ExecutionState &state,
                                     const llvm::Twine &message,
                                     const llvm::Twine &info="") {
        terminateStateOnError(state, message, Executor::Exec, NULL, info);
      }


      /*######## GRAVEYARD #######*/

      void doImpliedValueConcretization(ExecutionState &state,
                                        ref<Expr> e,
                                        ref<ConstantExpr> value);
  };
};

#endif //KLEE_EXECUTIONRUNNER_H
