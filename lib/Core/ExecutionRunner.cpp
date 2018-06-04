#include "Context.h"
#include "ExecutionRunner.h"
#include "Memory.h"
#include "MemoryManager.h"
#include "SpecialFunctionHandler.h"
#include "PTree.h"

#include "klee/Internal/ADT/RNG.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/util/ExprPPrinter.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/SmallPtrSet.h"

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/CallSite.h"
#include "CoreStats.h"

#else
#include "llvm/IR/CallSite.h"
#endif

using namespace llvm;
using namespace klee;

namespace {
  cl::opt<bool>
          ForkOnThreadScheduling("fork-on-thread-scheduling",
                                 cl::desc("Fork the states whenever the thread scheduling is not trivial"),
                                 cl::init(false));

  cl::opt<bool>
          ForkOnStatement("fork-on-statement",
                          cl::desc("Fork the current state whenever a possible thread scheduling can take place"),
                          cl::init(false));
}

RNG theRNG;

ExecutionRunner::ExecutionRunner(Executor* exec) : executor(exec) {
  solver = nullptr;
}

void ExecutionRunner::stepInstruction(ExecutionState &state) {
  // printDebugInstructions(state);

  //if (statsTracker)
  //  statsTracker->stepInstruction(state);

  Thread* thread = state.getCurrentThreadReference();

  //++stats::instructions;
  //++state.steppedInstructions;
  thread->prevPc = thread->pc;
  ++thread->pc;

  //if (stats::instructions==StopAfterNInstructions)
  //  haltExecution = true;
}

const Cell& ExecutionRunner::eval(KInstruction *ki, unsigned index,
                                  ExecutionState &state) const {
  assert(index < ki->inst->getNumOperands());
  int vnumber = ki->operands[index];

  assert(vnumber != -1 &&
         "Invalid operand to eval(), not a value or constant!");

  // Determine if this is a constant or not.
  if (vnumber < 0) {
    unsigned index = -vnumber - 2;
    return executor->kmodule->constantTable[index];
  } else {
    unsigned index = vnumber;
    Thread* thread = state.getCurrentThreadReference();
    StackFrame &sf = thread->stack.back();

    if (sf.locals[index].value.get() == nullptr) {
      klee_warning("Null pointer");
    }

    return sf.locals[index];
  }
}

void ExecutionRunner::bindLocal(KInstruction *target, ExecutionState &state,
                         ref<Expr> value) {
  getDestCell(state, target).value = value;
}

void ExecutionRunner::bindArgument(KFunction *kf, unsigned index,
                            ExecutionState &state, ref<Expr> value) {
  getArgumentCell(state, kf, index).value = value;
}

ref<Expr> ExecutionRunner::toUnique(const ExecutionState &state,
                             ref<Expr> &e) {
  ref<Expr> result = e;

  if (!isa<ConstantExpr>(e)) {
    ref<ConstantExpr> value;
    bool isTrue = false;

    solver->setTimeout(executor->coreSolverTimeout);
    if (solver->getValue(state, e, value) &&
        solver->mustBeTrue(state, EqExpr::create(e, value), isTrue) &&
        isTrue)
      result = value;
    solver->setTimeout(0);
  }

  return result;
}


/* Concretize the given expression, and return a possible constant value.
   'reason' is just a documentation string stating the reason for concretization. */
ref<klee::ConstantExpr>
ExecutionRunner::toConstant(ExecutionState &state,
                     ref<Expr> e,
                     const char *reason) {
  e = state.constraints.simplifyExpr(e);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(e))
    return CE;

  ref<ConstantExpr> value;
  bool success = solver->getValue(state, e, value);
  assert(success && "FIXME: Unhandled solver failure");
  (void) success;

  Thread* thread = state.getCurrentThreadReference();

  std::string str;
  llvm::raw_string_ostream os(str);

  os << "silently concretizing (reason: " << reason << ") expression " << e
     << " to value " << value << " (" << (*(thread->pc)).info->file << ":"
     << (*(thread->pc)).info->line << ")";

//  if (AllExternalWarnings)
//    klee_warning(reason, os.str().c_str());
//  else
    klee_warning_once(reason, "%s", os.str().c_str());

  addConstraint(state, EqExpr::create(e, value));

  return value;
}


void ExecutionRunner::addConstraint(ExecutionState &state, ref<Expr> condition) {
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(condition)) {
    if (!CE->isTrue())
      llvm::report_fatal_error("attempt to add invalid constraint");
    return;
  }

  // Check to see if this constraint violates seeds.
//  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it =
//          seedMap.find(&state);
//  if (it != seedMap.end()) {
//    bool warn = false;
//    for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
//                 siie = it->second.end(); siit != siie; ++siit) {
//      bool res;
//      bool success =
//              solver->mustBeFalse(state, siit->assignment.evaluate(condition), res);
//      assert(success && "FIXME: Unhandled solver failure");
//      (void) success;
//      if (res) {
//        siit->patchSeed(state, condition, solver);
//        warn = true;
//      }
//    }
//    if (warn)
//      klee_warning("seeds patched for violating constraint");
//  }

  state.addConstraint(condition);
  // Broken even in the old executor
  //if (ivcEnabled)
  //  doImpliedValueConcretization(state, condition,
  //                               ConstantExpr::alloc(1, Expr::Bool));
}

//void ExecutionRunner::executeGetValue(ExecutionState &state,
//                               ref<Expr> e,
//                               KInstruction *target) {
//  e = state.constraints.simplifyExpr(e);
//  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it =
//          seedMap.find(&state);
//  if (it==seedMap.end() || isa<ConstantExpr>(e)) {
//    ref<ConstantExpr> value;
//    bool success = solver->getValue(state, e, value);
//    assert(success && "FIXME: Unhandled solver failure");
//    (void) success;
//    bindLocal(target, state, value);
//  } else {
//    std::set< ref<Expr> > values;
//    for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
//                 siie = it->second.end(); siit != siie; ++siit) {
//      ref<ConstantExpr> value;
//      bool success =
//              solver->getValue(state, siit->assignment.evaluate(e), value);
//      assert(success && "FIXME: Unhandled solver failure");
//      (void) success;
//      values.insert(value);
//    }
//
//    std::vector< ref<Expr> > conditions;
//    for (std::set< ref<Expr> >::iterator vit = values.begin(),
//                 vie = values.end(); vit != vie; ++vit)
//      conditions.push_back(EqExpr::create(e, *vit));
//
//    std::vector<ExecutionState*> branches;
//    branch(state, conditions, branches);
//
//    std::vector<ExecutionState*>::iterator bit = branches.begin();
//    for (std::set< ref<Expr> >::iterator vit = values.begin(),
//                 vie = values.end(); vit != vie; ++vit) {
//      ExecutionState *es = *bit;
//      if (es)
//        bindLocal(target, *es, *vit);
//      ++bit;
//    }
//  }
//}

/// Compute the true target of a function call, resolving LLVM and KLEE aliases
/// and bitcasts.
Function* ExecutionRunner::getTargetFunction(Value *calledVal, ExecutionState &state) {
  SmallPtrSet<const GlobalValue*, 3> Visited;

  Constant *c = dyn_cast<Constant>(calledVal);
  if (!c)
    return 0;

  while (true) {
    if (GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 6)
      if (!Visited.insert(gv).second)
        return 0;
#else
      if (!Visited.insert(gv))
        return 0;
#endif
      std::string alias = state.getFnAlias(gv->getName());
      if (alias != "") {
        llvm::Module* currModule = executor->kmodule->module;
        GlobalValue *old_gv = gv;
        gv = currModule->getNamedValue(alias);
        if (!gv) {
          klee_error("Function %s(), alias for %s not found!\n", alias.c_str(),
                     old_gv->getName().str().c_str());
        }
      }

      if (Function *f = dyn_cast<Function>(gv))
        return f;
      else if (GlobalAlias *ga = dyn_cast<GlobalAlias>(gv))
        c = ga->getAliasee();
      else
        return 0;
    } else if (llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
      if (ce->getOpcode()==Instruction::BitCast)
        c = ce->getOperand(0);
      else
        return 0;
    } else
      return 0;
  }
}

/// TODO remove?
static bool isDebugIntrinsic(const Function *f, KModule *KM) {
  return false;
}

void ExecutionRunner::transferToBasicBlock(BasicBlock *dst, BasicBlock *src,
                                           ExecutionState &state) {
  // Note that in general phi nodes can reuse phi values from the same
  // block but the incoming value is the eval() result *before* the
  // execution of any phi nodes. this is pathological and doesn't
  // really seem to occur, but just in case we run the PhiCleanerPass
  // which makes sure this cannot happen and so it is safe to just
  // eval things in order. The PhiCleanerPass also makes sure that all
  // incoming blocks have the same order for each PHINode so we only
  // have to compute the index once.
  //
  // With that done we simply set an index in the state so that PHI
  // instructions know which argument to eval, set the pc, and continue.

  Thread* thread = state.getCurrentThreadReference();

  // XXX this lookup has to go ?
  KFunction *kf = thread->stack.back().kf;
  unsigned entry = kf->basicBlockEntry[dst];
  thread->pc = &kf->instructions[entry];
  if (thread->pc->inst->getOpcode() == Instruction::PHI) {
    PHINode *first = static_cast<PHINode*>(thread->pc->inst);
    thread->incomingBBIndex = first->getBasicBlockIndex(src);
  }
}

ObjectState *ExecutionRunner::bindObjectInState(ExecutionState &state,
                                                const MemoryObject *mo,
                                                bool isLocal,
                                                const Array *array) {
  ObjectState *os = array ? new ObjectState(mo, array) : new ObjectState(mo);
  state.addressSpace.bindObject(mo, os);

  // Its possible that multiple bindings of the same mo in the state
  // will put multiple copies on this list, but it doesn't really
  // matter because all we use this list for is to unbind the object
  // on function return.
  if (isLocal) {
    Thread* thread = state.getCurrentThreadReference();
    thread->stack.back().allocas.push_back(mo);
  }

  return os;
}

static inline const llvm::fltSemantics * fpWidthToSemantics(unsigned width) {
  switch(width) {
    case Expr::Int32:
      return &llvm::APFloat::IEEEsingle;
    case Expr::Int64:
      return &llvm::APFloat::IEEEdouble;
    case Expr::Fl80:
      return &llvm::APFloat::x87DoubleExtended;
    default:
      return 0;
  }
}

void ExecutionRunner::executeCall(ExecutionState &state,
                                  KInstruction *ki,
                                  Function *f,
                                  std::vector< ref<Expr> > &arguments) {
  Instruction *i = nullptr;
  Thread* thread = state.getCurrentThreadReference();

  if (ki)
    i = ki->inst;

  if (ki && f && f->isDeclaration()) {
    switch(f->getIntrinsicID()) {
      case Intrinsic::not_intrinsic:
        // state may be destroyed by this call, cannot touch
        callExternalFunction(state, ki, f, arguments);
        break;

        // va_arg is handled by caller and intrinsic lowering, see comment for
        // ExecutionState::varargs
      case Intrinsic::vastart:  {
        StackFrame &sf = thread->stack.back();

        // varargs can be zero if no varargs were provided
        if (!sf.varargs)
          return;

        // FIXME: This is really specific to the architecture, not the pointer
        // size. This happens to work for x86-32 and x86-64, however.
        Expr::Width WordSize = Context::get().getPointerWidth();
        if (WordSize == Expr::Int32) {
          executeMemoryOperation(state, true, arguments[0],
                                 sf.varargs->getBaseExpr(), 0);
        } else {
          assert(WordSize == Expr::Int64 && "Unknown word size!");

          // x86-64 has quite complicated calling convention. However,
          // instead of implementing it, we can do a simple hack: just
          // make a function believe that all varargs are on stack.
          executeMemoryOperation(state, true, arguments[0],
                                 ConstantExpr::create(48, 32), 0); // gp_offset
          executeMemoryOperation(state, true,
                                 AddExpr::create(arguments[0],
                                                 ConstantExpr::create(4, 64)),
                                 ConstantExpr::create(304, 32), 0); // fp_offset
          executeMemoryOperation(state, true,
                                 AddExpr::create(arguments[0],
                                                 ConstantExpr::create(8, 64)),
                                 sf.varargs->getBaseExpr(), 0); // overflow_arg_area
          executeMemoryOperation(state, true,
                                 AddExpr::create(arguments[0],
                                                 ConstantExpr::create(16, 64)),
                                 ConstantExpr::create(0, 64), 0); // reg_save_area
        }
        break;
      }
      case Intrinsic::vaend:
        // va_end is a noop for the interpreter.
        //
        // FIXME: We should validate that the target didn't do something bad
        // with va_end, however (like call it twice).
        break;

      case Intrinsic::vacopy:
        // va_copy should have been lowered.
        //
        // FIXME: It would be nice to check for errors in the usage of this as
        // well.
      default:
        klee_error("unknown intrinsic: %s", f->getName().data());
    }

    if (InvokeInst *ii = dyn_cast<InvokeInst>(i))
      transferToBasicBlock(ii->getNormalDest(), i->getParent(), state);
  } else {
    // FIXME: I'm not really happy about this reliance on prevPC but it is ok, I
    // guess. This just done to avoid having to pass KInstIterator everywhere
    // instead of the actual instruction, since we can't make a KInstIterator
    // from just an instruction (unlike LLVM).
    KFunction *kf = executor->kmodule->functionMap[f];
    thread->pushFrame(thread->prevPc, kf);
    thread->pc = kf->instructions;

    //if (statsTracker) {
    //  StackFrame* current = &thread->stack.back();
    //  statsTracker->framePushed(current, &thread->stack[thread->stack.size() - 2]);
    //}

    // TODO: support "byval" parameter attribute
    // TODO: support zeroext, signext, sret attributes

    unsigned callingArgs = arguments.size();
    unsigned funcArgs = f->arg_size();
    if (!f->isVarArg()) {
      if (callingArgs > funcArgs) {
        klee_warning_once(f, "calling %s with extra arguments.",
                          f->getName().data());
      } else if (callingArgs < funcArgs) {
        terminateStateOnError(state, "calling function with too few arguments",
                              Executor::User);
        return;
      }
    } else {
      Expr::Width WordSize = Context::get().getPointerWidth();

      if (callingArgs < funcArgs) {
        terminateStateOnError(state, "calling function with too few arguments",
                              Executor::User);
        return;
      }

      StackFrame &sf = thread->stack.back();
      unsigned size = 0;
      bool requires16ByteAlignment = false;
      for (unsigned i = funcArgs; i < callingArgs; i++) {
        // FIXME: This is really specific to the architecture, not the pointer
        // size. This happens to work for x86-32 and x86-64, however.
        if (WordSize == Expr::Int32) {
          size += Expr::getMinBytesForWidth(arguments[i]->getWidth());
        } else {
          Expr::Width argWidth = arguments[i]->getWidth();
          // AMD64-ABI 3.5.7p5: Step 7. Align l->overflow_arg_area upwards to a
          // 16 byte boundary if alignment needed by type exceeds 8 byte
          // boundary.
          //
          // Alignment requirements for scalar types is the same as their size
          if (argWidth > Expr::Int64) {
            size = llvm::RoundUpToAlignment(size, 16);
            requires16ByteAlignment = true;
          }
          size += llvm::RoundUpToAlignment(argWidth, WordSize) / 8;
        }
      }

      MemoryObject *mo = sf.varargs =
                                 executor->memory->allocate(size, true, false, thread->prevPc->inst,
                                                  (requires16ByteAlignment ? 16 : 8));
      if (!mo && size) {
        terminateStateOnExecError(state, "out of memory (varargs)");
        return;
      }

      if (mo) {
        if ((WordSize == Expr::Int64) && (mo->address & 15) &&
            requires16ByteAlignment) {
          // Both 64bit Linux/Glibc and 64bit MacOSX should align to 16 bytes.
          klee_warning_once(
                  0, "While allocating varargs: malloc did not align to 16 bytes.");
        }

        ObjectState *os = bindObjectInState(state, mo, true);
        unsigned offset = 0;
        for (unsigned i = funcArgs; i < callingArgs; i++) {
          // FIXME: This is really specific to the architecture, not the pointer
          // size. This happens to work for x86-32 and x86-64, however.
          if (WordSize == Expr::Int32) {
            os->write(offset, arguments[i]);
            offset += Expr::getMinBytesForWidth(arguments[i]->getWidth());
          } else {
            assert(WordSize == Expr::Int64 && "Unknown word size!");

            Expr::Width argWidth = arguments[i]->getWidth();
            if (argWidth > Expr::Int64) {
              offset = llvm::RoundUpToAlignment(offset, 16);
            }
            os->write(offset, arguments[i]);
            offset += llvm::RoundUpToAlignment(argWidth, WordSize) / 8;
          }
        }
      }
    }

    unsigned numFormals = f->arg_size();
    for (unsigned i=0; i<numFormals; ++i)
      bindArgument(kf, i, state, arguments[i]);
  }
}

void ExecutionRunner::executeInstruction(ExecutionState &state, KInstruction *ki) {
  Instruction *i = ki->inst;
  Thread* thread = state.getCurrentThreadReference();

  switch (i->getOpcode()) {
    // Control flow
    case Instruction::Ret: {
      ReturnInst *ri = cast<ReturnInst>(i);
      KInstIterator kcaller = thread->stack.back().caller;
      Instruction *caller = kcaller ? kcaller->inst : 0;
      bool isVoidReturn = (ri->getNumOperands() == 0);
      ref<Expr> result = ConstantExpr::alloc(0, Expr::Bool);

      if (!isVoidReturn) {
        result = eval(ki, 0, state).value;
      }

      if (thread->stack.size() <= 1) {
        assert(!caller && "caller set on initial stack frame");
        state.exitThread(thread->getThreadId());
        scheduleThreads(state);
      } else {
        state.popFrameOfCurrentThread();

        //if (statsTracker)
        //  statsTracker->framePopped(state);

        if (InvokeInst *ii = dyn_cast<InvokeInst>(caller)) {
          transferToBasicBlock(ii->getNormalDest(), caller->getParent(), state);
        } else {
          thread->pc = kcaller;
          ++thread->pc;
        }

        if (!isVoidReturn) {
          Type *t = caller->getType();
          if (t != Type::getVoidTy(i->getContext())) {
            // may need to do coercion due to bitcasts
            Expr::Width from = result->getWidth();
            Expr::Width to = executor->getWidthForLLVMType(t);

            if (from != to) {
              CallSite cs = (isa<InvokeInst>(caller) ? CallSite(cast<InvokeInst>(caller)) :
                             CallSite(cast<CallInst>(caller)));

              // XXX need to check other param attrs ?
              bool isSExt = cs.paramHasAttr(0, llvm::Attribute::SExt);
              if (isSExt) {
                result = SExtExpr::create(result, to);
              } else {
                result = ZExtExpr::create(result, to);
              }
            }

            bindLocal(kcaller, state, result);
          }
        } else {
          // We check that the return value has no users instead of
          // checking the type, since C defaults to returning int for
          // undeclared functions.
          if (!caller->use_empty()) {
            terminateStateOnExecError(state, "return void when caller expected a result");
          }
        }
      }
      break;
    }
    case Instruction::Br: {
      BranchInst *bi = cast<BranchInst>(i);
      if (bi->isUnconditional()) {
        transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), state);
      } else {
        // FIXME: Find a way that we don't have this hidden dependency.
        assert(bi->getCondition() == bi->getOperand(0) &&
               "Wrong operand index!");
        ref<Expr> cond = eval(ki, 0, state).value;
        Executor::StatePair branches = fork(state, cond, false);

        // NOTE: There is a hidden dependency here, markBranchVisited
        // requires that we still be in the context of the branch
        // instruction (it reuses its statistic id). Should be cleaned
        // up with convenient instruction specific data.
        //if (statsTracker && thread->stack.back().kf->trackCoverage)
        //  statsTracker->markBranchVisited(branches.first, branches.second);

        if (branches.first)
          transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), *branches.first);
        if (branches.second)
          transferToBasicBlock(bi->getSuccessor(1), bi->getParent(), *branches.second);
      }
      break;
    }
    case Instruction::IndirectBr: {
      // implements indirect branch to a label within the current function
      const auto bi = cast<IndirectBrInst>(i);
      auto address = eval(ki, 0, state).value;
      address = toUnique(state, address);

      // concrete address
      if (const auto CE = dyn_cast<ConstantExpr>(address.get())) {
        const auto bb_address = (BasicBlock *) CE->getZExtValue(Context::get().getPointerWidth());
        transferToBasicBlock(bb_address, bi->getParent(), state);
        break;
      }

      // symbolic address
      const auto numDestinations = bi->getNumDestinations();
      std::vector<BasicBlock *> targets;
      targets.reserve(numDestinations);
      std::vector<ref<Expr>> expressions;
      expressions.reserve(numDestinations);

      ref<Expr> errorCase = ConstantExpr::alloc(1, Expr::Bool);
      SmallPtrSet<BasicBlock *, 5> destinations;
      // collect and check destinations from label list
      for (unsigned k = 0; k < numDestinations; ++k) {
        // filter duplicates
        const auto d = bi->getDestination(k);
        if (destinations.count(d)) continue;
        destinations.insert(d);

        // create address expression
        const auto PE = Expr::createPointer(reinterpret_cast<std::uint64_t>(d));
        ref<Expr> e = EqExpr::create(address, PE);

        // exclude address from errorCase
        errorCase = AndExpr::create(errorCase, Expr::createIsZero(e));

        // check feasibility
        bool result;
        bool success __attribute__ ((unused)) = solver->mayBeTrue(state, e, result);
        assert(success && "FIXME: Unhandled solver failure");
        if (result) {
          targets.push_back(d);
          expressions.push_back(e);
        }
      }
      // check errorCase feasibility
      bool result;
      bool success __attribute__ ((unused)) = solver->mayBeTrue(state, errorCase, result);
      assert(success && "FIXME: Unhandled solver failure");
      if (result) {
        expressions.push_back(errorCase);
      }

      // fork states
      std::vector<ExecutionState *> branches;
      branch(state, expressions, branches);

      // terminate error state
      if (result) {
        terminateStateOnExecError(*branches.back(), "indirectbr: illegal label address");
        branches.pop_back();
      }

      // branch states to resp. target blocks
      assert(targets.size() == branches.size());
      for (std::vector<ExecutionState *>::size_type k = 0; k < branches.size(); ++k) {
        if (branches[k]) {
          transferToBasicBlock(targets[k], bi->getParent(), *branches[k]);
        }
      }

      break;
    }
    case Instruction::Switch: {
      SwitchInst *si = cast<SwitchInst>(i);
      ref<Expr> cond = eval(ki, 0, state).value;
      BasicBlock *bb = si->getParent();

      cond = toUnique(state, cond);
      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(cond)) {
        // Somewhat gross to create these all the time, but fine till we
        // switch to an internal rep.
        llvm::IntegerType *Ty = cast<IntegerType>(si->getCondition()->getType());
        ConstantInt *ci = ConstantInt::get(Ty, CE->getZExtValue());
        unsigned index = si->findCaseValue(ci).getSuccessorIndex();
        transferToBasicBlock(si->getSuccessor(index), si->getParent(), state);
      } else {
        // Handle possible different branch targets

        // We have the following assumptions:
        // - each case value is mutual exclusive to all other values including the
        //   default value
        // - order of case branches is based on the order of the expressions of
        //   the scase values, still default is handled last
        std::vector<BasicBlock *> bbOrder;
        std::map<BasicBlock *, ref<Expr> > branchTargets;

        std::map<ref<Expr>, BasicBlock *> expressionOrder;

        // Iterate through all non-default cases and order them by expressions
#if LLVM_VERSION_CODE > LLVM_VERSION(3, 4)
        for (auto i : si->cases()) {
#else
        for (SwitchInst::CaseIt i = si->case_begin(), e = si->case_end(); i != e;
             ++i) {
#endif
          ref<Expr> value = executor->evalConstant(i.getCaseValue());

          BasicBlock *caseSuccessor = i.getCaseSuccessor();
          expressionOrder.insert(std::make_pair(value, caseSuccessor));
        }

        // Track default branch values
        ref<Expr> defaultValue = ConstantExpr::alloc(1, Expr::Bool);

        // iterate through all non-default cases but in order of the expressions
        for (std::map<ref<Expr>, BasicBlock *>::iterator
                     it = expressionOrder.begin(),
                     itE = expressionOrder.end();
             it != itE; ++it) {
          ref<Expr> match = EqExpr::create(cond, it->first);

          // Make sure that the default value does not contain this target's value
          defaultValue = AndExpr::create(defaultValue, Expr::createIsZero(match));

          // Check if control flow could take this case
          bool result;
          bool success = solver->mayBeTrue(state, match, result);
          assert(success && "FIXME: Unhandled solver failure");
          (void) success;
          if (result) {
            BasicBlock *caseSuccessor = it->second;

            // Handle the case that a basic block might be the target of multiple
            // switch cases.
            // Currently we generate an expression containing all switch-case
            // values for the same target basic block. We spare us forking too
            // many times but we generate more complex condition expressions
            // TODO Add option to allow to choose between those behaviors
            std::pair<std::map<BasicBlock *, ref<Expr> >::iterator, bool> res =
                    branchTargets.insert(std::make_pair(
                            caseSuccessor, ConstantExpr::alloc(0, Expr::Bool)));

            res.first->second = OrExpr::create(match, res.first->second);

            // Only add basic blocks which have not been target of a branch yet
            if (res.second) {
              bbOrder.push_back(caseSuccessor);
            }
          }
        }

        // Check if control could take the default case
        bool res;
        bool success = solver->mayBeTrue(state, defaultValue, res);
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        if (res) {
          std::pair<std::map<BasicBlock *, ref<Expr> >::iterator, bool> ret =
                  branchTargets.insert(
                          std::make_pair(si->getDefaultDest(), defaultValue));
          if (ret.second) {
            bbOrder.push_back(si->getDefaultDest());
          }
        }

        // Fork the current state with each state having one of the possible
        // successors of this switch
        std::vector< ref<Expr> > conditions;
        for (std::vector<BasicBlock *>::iterator it = bbOrder.begin(),
                     ie = bbOrder.end();
             it != ie; ++it) {
          conditions.push_back(branchTargets[*it]);
        }
        std::vector<ExecutionState*> branches;
        branch(state, conditions, branches);

        std::vector<ExecutionState*>::iterator bit = branches.begin();
        for (std::vector<BasicBlock *>::iterator it = bbOrder.begin(),
                     ie = bbOrder.end();
             it != ie; ++it) {
          ExecutionState *es = *bit;
          if (es)
            transferToBasicBlock(*it, bb, *es);
          ++bit;
        }
      }
      break;
    }
    case Instruction::Unreachable:
      // Note that this is not necessarily an internal bug, llvm will
      // generate unreachable instructions in cases where it knows the
      // program will crash. So it is effectively a SEGV or internal
      // error.
      terminateStateOnExecError(state, "reached \"unreachable\" instruction");
      break;

    case Instruction::Invoke:
    case Instruction::Call: {
      CallSite cs(i);

      unsigned numArgs = cs.arg_size();
      Value *fp = cs.getCalledValue();
      Function *f = getTargetFunction(fp, state);

      // Skip debug intrinsics, we can't evaluate their metadata arguments.
      if (f && isDebugIntrinsic(f, executor->kmodule))
        break;

      if (isa<InlineAsm>(fp)) {
        terminateStateOnExecError(state, "inline assembly is unsupported");
        break;
      }
      // evaluate arguments
      std::vector< ref<Expr> > arguments;
      arguments.reserve(numArgs);

      for (unsigned j=0; j<numArgs; ++j)
        arguments.push_back(eval(ki, j+1, state).value);

      if (f) {
        const FunctionType *fType =
                dyn_cast<FunctionType>(cast<PointerType>(f->getType())->getElementType());
        const FunctionType *fpType =
                dyn_cast<FunctionType>(cast<PointerType>(fp->getType())->getElementType());

        // special case the call with a bitcast case
        if (fType != fpType) {
          assert(fType && fpType && "unable to get function type");

          // XXX check result coercion

          // XXX this really needs thought and validation
          unsigned i=0;
          for (std::vector< ref<Expr> >::iterator
                       ai = arguments.begin(), ie = arguments.end();
               ai != ie; ++ai) {
            Expr::Width to, from = (*ai)->getWidth();

            if (i<fType->getNumParams()) {
              to = executor->getWidthForLLVMType(fType->getParamType(i));

              if (from != to) {
                // XXX need to check other param attrs ?
                bool isSExt = cs.paramHasAttr(i+1, llvm::Attribute::SExt);
                if (isSExt) {
                  arguments[i] = SExtExpr::create(arguments[i], to);
                } else {
                  arguments[i] = ZExtExpr::create(arguments[i], to);
                }
              }
            }

            i++;
          }
        }

        executeCall(state, ki, f, arguments);
      } else {
        ref<Expr> v = eval(ki, 0, state).value;

        ExecutionState *free = &state;
        bool hasInvalid = false, first = true;

        /* XXX This is wasteful, no need to do a full evaluate since we
           have already got a value. But in the end the caches should
           handle it for us, albeit with some overhead. */
        do {
          ref<ConstantExpr> value;
          bool success = solver->getValue(*free, v, value);
          assert(success && "FIXME: Unhandled solver failure");
          (void) success;
          Executor::StatePair res = fork(*free, EqExpr::create(v, value), true);
          if (res.first) {
            uint64_t addr = value->getZExtValue();
            if (executor->legalFunctions.count(addr)) {
              f = (Function*) addr;

              // Don't give warning on unique resolution
              if (res.second || !first)
                klee_warning_once(reinterpret_cast<void*>(addr),
                                  "resolved symbolic function pointer to: %s",
                                  f->getName().data());

              executeCall(*res.first, ki, f, arguments);
            } else {
              if (!hasInvalid) {
                terminateStateOnExecError(state, "invalid function pointer");
                hasInvalid = true;
              }
            }
          }

          first = false;
          free = res.second;
        } while (free);
      }
      break;
    }
    case Instruction::PHI: {
      ref<Expr> result = eval(ki, thread->incomingBBIndex, state).value;
      bindLocal(ki, state, result);
      break;
    }

      // Special instructions
    case Instruction::Select: {
      // NOTE: It is not required that operands 1 and 2 be of scalar type.
      ref<Expr> cond = eval(ki, 0, state).value;
      ref<Expr> tExpr = eval(ki, 1, state).value;
      ref<Expr> fExpr = eval(ki, 2, state).value;
      ref<Expr> result = SelectExpr::create(cond, tExpr, fExpr);
      bindLocal(ki, state, result);
      break;
    }

    case Instruction::VAArg:
      terminateStateOnExecError(state, "unexpected VAArg instruction");
      break;

      // Arithmetic / logical

    case Instruction::Add: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      bindLocal(ki, state, AddExpr::create(left, right));
      break;
    }

    case Instruction::Sub: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      bindLocal(ki, state, SubExpr::create(left, right));
      break;
    }

    case Instruction::Mul: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      bindLocal(ki, state, MulExpr::create(left, right));
      break;
    }

    case Instruction::UDiv: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UDivExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case Instruction::SDiv: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SDivExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case Instruction::URem: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = URemExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case Instruction::SRem: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SRemExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case Instruction::And: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = AndExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case Instruction::Or: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = OrExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case Instruction::Xor: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = XorExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case Instruction::Shl: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = ShlExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case Instruction::LShr: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = LShrExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case Instruction::AShr: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = AShrExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

      // Compare

    case Instruction::ICmp: {
      CmpInst *ci = cast<CmpInst>(i);
      ICmpInst *ii = cast<ICmpInst>(ci);

      switch(ii->getPredicate()) {
        case ICmpInst::ICMP_EQ: {
          ref<Expr> left = eval(ki, 0, state).value;
          ref<Expr> right = eval(ki, 1, state).value;
          ref<Expr> result = EqExpr::create(left, right);
          bindLocal(ki, state, result);
          break;
        }

        case ICmpInst::ICMP_NE: {
          ref<Expr> left = eval(ki, 0, state).value;
          ref<Expr> right = eval(ki, 1, state).value;
          ref<Expr> result = NeExpr::create(left, right);
          bindLocal(ki, state, result);
          break;
        }

        case ICmpInst::ICMP_UGT: {
          ref<Expr> left = eval(ki, 0, state).value;
          ref<Expr> right = eval(ki, 1, state).value;
          ref<Expr> result = UgtExpr::create(left, right);
          bindLocal(ki, state,result);
          break;
        }

        case ICmpInst::ICMP_UGE: {
          ref<Expr> left = eval(ki, 0, state).value;
          ref<Expr> right = eval(ki, 1, state).value;
          ref<Expr> result = UgeExpr::create(left, right);
          bindLocal(ki, state, result);
          break;
        }

        case ICmpInst::ICMP_ULT: {
          ref<Expr> left = eval(ki, 0, state).value;
          ref<Expr> right = eval(ki, 1, state).value;
          ref<Expr> result = UltExpr::create(left, right);
          bindLocal(ki, state, result);
          break;
        }

        case ICmpInst::ICMP_ULE: {
          ref<Expr> left = eval(ki, 0, state).value;
          ref<Expr> right = eval(ki, 1, state).value;
          ref<Expr> result = UleExpr::create(left, right);
          bindLocal(ki, state, result);
          break;
        }

        case ICmpInst::ICMP_SGT: {
          ref<Expr> left = eval(ki, 0, state).value;
          ref<Expr> right = eval(ki, 1, state).value;
          ref<Expr> result = SgtExpr::create(left, right);
          bindLocal(ki, state, result);
          break;
        }

        case ICmpInst::ICMP_SGE: {
          ref<Expr> left = eval(ki, 0, state).value;
          ref<Expr> right = eval(ki, 1, state).value;
          ref<Expr> result = SgeExpr::create(left, right);
          bindLocal(ki, state, result);
          break;
        }

        case ICmpInst::ICMP_SLT: {
          ref<Expr> left = eval(ki, 0, state).value;
          ref<Expr> right = eval(ki, 1, state).value;
          ref<Expr> result = SltExpr::create(left, right);
          bindLocal(ki, state, result);
          break;
        }

        case ICmpInst::ICMP_SLE: {
          ref<Expr> left = eval(ki, 0, state).value;
          ref<Expr> right = eval(ki, 1, state).value;
          ref<Expr> result = SleExpr::create(left, right);
          bindLocal(ki, state, result);
          break;
        }

        default:
          terminateStateOnExecError(state, "invalid ICmp predicate");
      }
      break;
    }

      // Memory instructions...
    case Instruction::Alloca: {
      AllocaInst *ai = cast<AllocaInst>(i);
      unsigned elementSize =
              executor->kmodule->targetData->getTypeStoreSize(ai->getAllocatedType());
      ref<Expr> size = Expr::createPointer(elementSize);
      if (ai->isArrayAllocation()) {
        ref<Expr> count = eval(ki, 0, state).value;
        count = Expr::createZExtToPointerWidth(count);
        size = MulExpr::create(size, count);
      }
      executeAlloc(state, size, true, ki);
      break;
    }

    case Instruction::Load: {
      ref<Expr> base = eval(ki, 0, state).value;
      executeMemoryOperation(state, false, base, 0, ki);
      break;
    }
    case Instruction::Store: {
      ref<Expr> base = eval(ki, 1, state).value;
      ref<Expr> value = eval(ki, 0, state).value;
      executeMemoryOperation(state, true, base, value, 0);
      break;
    }

    case Instruction::GetElementPtr: {
      KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
      ref<Expr> base = eval(ki, 0, state).value;

      for (std::vector< std::pair<unsigned, uint64_t> >::iterator
                   it = kgepi->indices.begin(), ie = kgepi->indices.end();
           it != ie; ++it) {
        uint64_t elementSize = it->second;
        ref<Expr> index = eval(ki, it->first, state).value;
        base = AddExpr::create(base,
                               MulExpr::create(Expr::createSExtToPointerWidth(index),
                                               Expr::createPointer(elementSize)));
      }
      if (kgepi->offset)
        base = AddExpr::create(base,
                               Expr::createPointer(kgepi->offset));
      bindLocal(ki, state, base);
      break;
    }

      // Conversion
    case Instruction::Trunc: {
      CastInst *ci = cast<CastInst>(i);
      ref<Expr> result = ExtractExpr::create(eval(ki, 0, state).value,
                                             0,
                                             executor->getWidthForLLVMType(ci->getType()));
      bindLocal(ki, state, result);
      break;
    }
    case Instruction::ZExt: {
      CastInst *ci = cast<CastInst>(i);
      ref<Expr> result = ZExtExpr::create(eval(ki, 0, state).value,
                                          executor->getWidthForLLVMType(ci->getType()));
      bindLocal(ki, state, result);
      break;
    }
    case Instruction::SExt: {
      CastInst *ci = cast<CastInst>(i);
      ref<Expr> result = SExtExpr::create(eval(ki, 0, state).value,
                                          executor->getWidthForLLVMType(ci->getType()));
      bindLocal(ki, state, result);
      break;
    }

    case Instruction::IntToPtr: {
      CastInst *ci = cast<CastInst>(i);
      Expr::Width pType = executor->getWidthForLLVMType(ci->getType());
      ref<Expr> arg = eval(ki, 0, state).value;
      bindLocal(ki, state, ZExtExpr::create(arg, pType));
      break;
    }
    case Instruction::PtrToInt: {
      CastInst *ci = cast<CastInst>(i);
      Expr::Width iType = executor->getWidthForLLVMType(ci->getType());
      ref<Expr> arg = eval(ki, 0, state).value;
      bindLocal(ki, state, ZExtExpr::create(arg, iType));
      break;
    }

    case Instruction::BitCast: {
      ref<Expr> result = eval(ki, 0, state).value;
      bindLocal(ki, state, result);
      break;
    }

      // Floating point instructions

    case Instruction::FAdd: {
      ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                          "floating point");
      ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                           "floating point");
      if (!fpWidthToSemantics(left->getWidth()) ||
          !fpWidthToSemantics(right->getWidth()))
        return terminateStateOnExecError(state, "Unsupported FAdd operation");

      llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
      Res.add(APFloat(*fpWidthToSemantics(right->getWidth()),right->getAPValue()), APFloat::rmNearestTiesToEven);
      bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
      break;
    }

    case Instruction::FSub: {
      ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                          "floating point");
      ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                           "floating point");
      if (!fpWidthToSemantics(left->getWidth()) ||
          !fpWidthToSemantics(right->getWidth()))
        return terminateStateOnExecError(state, "Unsupported FSub operation");
      llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
      Res.subtract(APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()), APFloat::rmNearestTiesToEven);
      bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
      break;
    }

    case Instruction::FMul: {
      ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                          "floating point");
      ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                           "floating point");
      if (!fpWidthToSemantics(left->getWidth()) ||
          !fpWidthToSemantics(right->getWidth()))
        return terminateStateOnExecError(state, "Unsupported FMul operation");

      llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
      Res.multiply(APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()), APFloat::rmNearestTiesToEven);
      bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
      break;
    }

    case Instruction::FDiv: {
      ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                          "floating point");
      ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                           "floating point");
      if (!fpWidthToSemantics(left->getWidth()) ||
          !fpWidthToSemantics(right->getWidth()))
        return terminateStateOnExecError(state, "Unsupported FDiv operation");

      llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
      Res.divide(APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()), APFloat::rmNearestTiesToEven);
      bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
      break;
    }

    case Instruction::FRem: {
      ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                          "floating point");
      ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                           "floating point");
      if (!fpWidthToSemantics(left->getWidth()) ||
          !fpWidthToSemantics(right->getWidth()))
        return terminateStateOnExecError(state, "Unsupported FRem operation");
      llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
      Res.mod(APFloat(*fpWidthToSemantics(right->getWidth()),right->getAPValue()),
              APFloat::rmNearestTiesToEven);
      bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
      break;
    }

    case Instruction::FPTrunc: {
      FPTruncInst *fi = cast<FPTruncInst>(i);
      Expr::Width resultType = executor->getWidthForLLVMType(fi->getType());
      ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                         "floating point");
      if (!fpWidthToSemantics(arg->getWidth()) || resultType > arg->getWidth())
        return terminateStateOnExecError(state, "Unsupported FPTrunc operation");

      llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
      bool losesInfo = false;
      Res.convert(*fpWidthToSemantics(resultType),
                  llvm::APFloat::rmNearestTiesToEven,
                  &losesInfo);
      bindLocal(ki, state, ConstantExpr::alloc(Res));
      break;
    }

    case Instruction::FPExt: {
      FPExtInst *fi = cast<FPExtInst>(i);
      Expr::Width resultType = executor->getWidthForLLVMType(fi->getType());
      ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                         "floating point");
      if (!fpWidthToSemantics(arg->getWidth()) || arg->getWidth() > resultType)
        return terminateStateOnExecError(state, "Unsupported FPExt operation");
      llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
      bool losesInfo = false;
      Res.convert(*fpWidthToSemantics(resultType),
                  llvm::APFloat::rmNearestTiesToEven,
                  &losesInfo);
      bindLocal(ki, state, ConstantExpr::alloc(Res));
      break;
    }

    case Instruction::FPToUI: {
      FPToUIInst *fi = cast<FPToUIInst>(i);
      Expr::Width resultType = executor->getWidthForLLVMType(fi->getType());
      ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                         "floating point");
      if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
        return terminateStateOnExecError(state, "Unsupported FPToUI operation");

      llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
      uint64_t value = 0;
      bool isExact = true;
      Arg.convertToInteger(&value, resultType, false,
                           llvm::APFloat::rmTowardZero, &isExact);
      bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
      break;
    }

    case Instruction::FPToSI: {
      FPToSIInst *fi = cast<FPToSIInst>(i);
      Expr::Width resultType = executor->getWidthForLLVMType(fi->getType());
      ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                         "floating point");
      if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
        return terminateStateOnExecError(state, "Unsupported FPToSI operation");
      llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());

      uint64_t value = 0;
      bool isExact = true;
      Arg.convertToInteger(&value, resultType, true,
                           llvm::APFloat::rmTowardZero, &isExact);
      bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
      break;
    }

    case Instruction::UIToFP: {
      UIToFPInst *fi = cast<UIToFPInst>(i);
      Expr::Width resultType = executor->getWidthForLLVMType(fi->getType());
      ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                         "floating point");
      const llvm::fltSemantics *semantics = fpWidthToSemantics(resultType);
      if (!semantics)
        return terminateStateOnExecError(state, "Unsupported UIToFP operation");
      llvm::APFloat f(*semantics, 0);
      f.convertFromAPInt(arg->getAPValue(), false,
                         llvm::APFloat::rmNearestTiesToEven);

      bindLocal(ki, state, ConstantExpr::alloc(f));
      break;
    }

    case Instruction::SIToFP: {
      SIToFPInst *fi = cast<SIToFPInst>(i);
      Expr::Width resultType = executor->getWidthForLLVMType(fi->getType());
      ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                         "floating point");
      const llvm::fltSemantics *semantics = fpWidthToSemantics(resultType);
      if (!semantics)
        return terminateStateOnExecError(state, "Unsupported SIToFP operation");
      llvm::APFloat f(*semantics, 0);
      f.convertFromAPInt(arg->getAPValue(), true,
                         llvm::APFloat::rmNearestTiesToEven);

      bindLocal(ki, state, ConstantExpr::alloc(f));
      break;
    }

    case Instruction::FCmp: {
      FCmpInst *fi = cast<FCmpInst>(i);
      ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                          "floating point");
      ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                           "floating point");
      if (!fpWidthToSemantics(left->getWidth()) ||
          !fpWidthToSemantics(right->getWidth()))
        return terminateStateOnExecError(state, "Unsupported FCmp operation");

      APFloat LHS(*fpWidthToSemantics(left->getWidth()),left->getAPValue());
      APFloat RHS(*fpWidthToSemantics(right->getWidth()),right->getAPValue());
      APFloat::cmpResult CmpRes = LHS.compare(RHS);

      bool Result = false;
      switch( fi->getPredicate() ) {
        // Predicates which only care about whether or not the operands are NaNs.
        case FCmpInst::FCMP_ORD:
          Result = (CmpRes != APFloat::cmpUnordered);
          break;

        case FCmpInst::FCMP_UNO:
          Result = (CmpRes == APFloat::cmpUnordered);
          break;

          // Ordered comparisons return false if either operand is NaN.  Unordered
          // comparisons return true if either operand is NaN.
        case FCmpInst::FCMP_UEQ:
          Result = (CmpRes == APFloat::cmpUnordered || CmpRes == APFloat::cmpEqual);
          break;
        case FCmpInst::FCMP_OEQ:
          Result = (CmpRes != APFloat::cmpUnordered && CmpRes == APFloat::cmpEqual);
          break;

        case FCmpInst::FCMP_UGT:
          Result = (CmpRes == APFloat::cmpUnordered || CmpRes == APFloat::cmpGreaterThan);
          break;
        case FCmpInst::FCMP_OGT:
          Result = (CmpRes != APFloat::cmpUnordered && CmpRes == APFloat::cmpGreaterThan);
          break;

        case FCmpInst::FCMP_UGE:
          Result = (CmpRes == APFloat::cmpUnordered || (CmpRes == APFloat::cmpGreaterThan || CmpRes == APFloat::cmpEqual));
          break;
        case FCmpInst::FCMP_OGE:
          Result = (CmpRes != APFloat::cmpUnordered && (CmpRes == APFloat::cmpGreaterThan || CmpRes == APFloat::cmpEqual));
          break;

        case FCmpInst::FCMP_ULT:
          Result = (CmpRes == APFloat::cmpUnordered || CmpRes == APFloat::cmpLessThan);
          break;
        case FCmpInst::FCMP_OLT:
          Result = (CmpRes != APFloat::cmpUnordered && CmpRes == APFloat::cmpLessThan);
          break;

        case FCmpInst::FCMP_ULE:
          Result = (CmpRes == APFloat::cmpUnordered || (CmpRes == APFloat::cmpLessThan || CmpRes == APFloat::cmpEqual));
          break;
        case FCmpInst::FCMP_OLE:
          Result = (CmpRes != APFloat::cmpUnordered && (CmpRes == APFloat::cmpLessThan || CmpRes == APFloat::cmpEqual));
          break;

        case FCmpInst::FCMP_UNE:
          Result = (CmpRes == APFloat::cmpUnordered || CmpRes != APFloat::cmpEqual);
          break;
        case FCmpInst::FCMP_ONE:
          Result = (CmpRes != APFloat::cmpUnordered && CmpRes != APFloat::cmpEqual);
          break;

        default:
          assert(0 && "Invalid FCMP predicate!");
          break;
        case FCmpInst::FCMP_FALSE:
          Result = false;
          break;
        case FCmpInst::FCMP_TRUE:
          Result = true;
          break;
      }

      bindLocal(ki, state, ConstantExpr::alloc(Result, Expr::Bool));
      break;
    }
    case Instruction::InsertValue: {
      KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

      ref<Expr> agg = eval(ki, 0, state).value;
      ref<Expr> val = eval(ki, 1, state).value;

      ref<Expr> l = NULL, r = NULL;
      unsigned lOffset = kgepi->offset*8, rOffset = kgepi->offset*8 + val->getWidth();

      if (lOffset > 0)
        l = ExtractExpr::create(agg, 0, lOffset);
      if (rOffset < agg->getWidth())
        r = ExtractExpr::create(agg, rOffset, agg->getWidth() - rOffset);

      ref<Expr> result;
      if (!l.isNull() && !r.isNull())
        result = ConcatExpr::create(r, ConcatExpr::create(val, l));
      else if (!l.isNull())
        result = ConcatExpr::create(val, l);
      else if (!r.isNull())
        result = ConcatExpr::create(r, val);
      else
        result = val;

      bindLocal(ki, state, result);
      break;
    }
    case Instruction::ExtractValue: {
      KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

      ref<Expr> agg = eval(ki, 0, state).value;

      ref<Expr> result = ExtractExpr::create(agg, kgepi->offset*8, executor->getWidthForLLVMType(i->getType()));

      bindLocal(ki, state, result);
      break;
    }
    case Instruction::Fence: {
      // Ignore for now
      break;
    }
    case Instruction::InsertElement: {
      InsertElementInst *iei = cast<InsertElementInst>(i);
      ref<Expr> vec = eval(ki, 0, state).value;
      ref<Expr> newElt = eval(ki, 1, state).value;
      ref<Expr> idx = eval(ki, 2, state).value;

      ConstantExpr *cIdx = dyn_cast<ConstantExpr>(idx);
      if (cIdx == NULL) {
        terminateStateOnError(
                state, "InsertElement, support for symbolic index not implemented",
                Executor::Unhandled);
        return;
      }
      uint64_t iIdx = cIdx->getZExtValue();
      const llvm::VectorType *vt = iei->getType();
      unsigned EltBits = executor->getWidthForLLVMType(vt->getElementType());

      if (iIdx >= vt->getNumElements()) {
        // Out of bounds write
        terminateStateOnError(state, "Out of bounds write when inserting element",
                              Executor::BadVectorAccess);
        return;
      }

      const unsigned elementCount = vt->getNumElements();
      llvm::SmallVector<ref<Expr>, 8> elems;
      elems.reserve(elementCount);
      for (unsigned i = elementCount; i != 0; --i) {
        auto of = i - 1;
        unsigned bitOffset = EltBits * of;
        elems.push_back(
                of == iIdx ? newElt : ExtractExpr::create(vec, bitOffset, EltBits));
      }

      assert(Context::get().isLittleEndian() && "FIXME:Broken for big endian");
      ref<Expr> Result = ConcatExpr::createN(elementCount, elems.data());
      bindLocal(ki, state, Result);
      break;
    }
    case Instruction::ExtractElement: {
      ExtractElementInst *eei = cast<ExtractElementInst>(i);
      ref<Expr> vec = eval(ki, 0, state).value;
      ref<Expr> idx = eval(ki, 1, state).value;

      ConstantExpr *cIdx = dyn_cast<ConstantExpr>(idx);
      if (cIdx == NULL) {
        terminateStateOnError(
                state, "ExtractElement, support for symbolic index not implemented",
                Executor::Unhandled);
        return;
      }
      uint64_t iIdx = cIdx->getZExtValue();
      const llvm::VectorType *vt = eei->getVectorOperandType();
      unsigned EltBits = executor->getWidthForLLVMType(vt->getElementType());

      if (iIdx >= vt->getNumElements()) {
        // Out of bounds read
        terminateStateOnError(state, "Out of bounds read when extracting element",
                              Executor::BadVectorAccess);
        return;
      }

      unsigned bitOffset = EltBits * iIdx;
      ref<Expr> Result = ExtractExpr::create(vec, bitOffset, EltBits);
      bindLocal(ki, state, Result);
      break;
    }
    case Instruction::ShuffleVector:
      // Should never happen due to Scalarizer pass removing ShuffleVector
      // instructions.
      terminateStateOnExecError(state, "Unexpected ShuffleVector instruction");
      break;
      // Other instructions...
      // Unhandled
    default:
      terminateStateOnExecError(state, "illegal instruction");
      break;
  }
}

void ExecutionRunner::stepInState(ExecutionState& state) {
  Thread *thread = state.getCurrentThreadReference();
  KInstruction *ki = thread->pc;

  state.hasScheduledThreads = false;
  stepInstruction(state);

  executeInstruction(state, ki);
  // processTimers(&state, MaxInstructionTime);

  bool shouldForkAfterStatement = false;
  if (ForkOnStatement) {
    auto itInRemoved = std::find(executor->removedStates.begin(), executor->removedStates.end(), &state);
    shouldForkAfterStatement = itInRemoved == executor->removedStates.end();
  }

  // We only want to fork if we do not have forked already
  if (shouldForkAfterStatement && !state.hasScheduledThreads) {
    scheduleThreads(state);
  }
}

// XXX shoot me
static const char *okExternalsList[] = { "printf",
                                         "fprintf",
                                         "puts",
                                         "getpid" };
static std::set<std::string> okExternals(okExternalsList,
                                         okExternalsList +
                                         (sizeof(okExternalsList)/sizeof(okExternalsList[0])));

void ExecutionRunner::callExternalFunction(ExecutionState &state,
                                           KInstruction *target,
                                           Function *function,
                                           std::vector< ref<Expr> > &arguments) {
  // check if specialFunctionHandler wants it
  if (specialFunctionHandler->handle(state, function, target, arguments))
    return;

  if (/*NoExternals */true && !okExternals.count(function->getName())) {
    klee_warning("Disallowed call to external function: %s\n",
                 function->getName().str().c_str());
    terminateStateOnError(state, "externals disallowed", Executor::User);
    return;
  }

//  // normal external function handling path
//  // allocate 128 bits for each argument (+return value) to support fp80's;
//  // we could iterate through all the arguments first and determine the exact
//  // size we need, but this is faster, and the memory usage isn't significant.
//  uint64_t *args = (uint64_t*) alloca(2*sizeof(*args) * (arguments.size() + 1));
//  memset(args, 0, 2 * sizeof(*args) * (arguments.size() + 1));
//  unsigned wordIndex = 2;
//  for (std::vector<ref<Expr> >::iterator ai = arguments.begin(),
//               ae = arguments.end(); ai!=ae; ++ai) {
//    if (AllowExternalSymCalls) { // don't bother checking uniqueness
//      ref<ConstantExpr> ce;
//      bool success = solver->getValue(state, *ai, ce);
//      assert(success && "FIXME: Unhandled solver failure");
//      (void) success;
//      ce->toMemory(&args[wordIndex]);
//      ObjectPair op;
//      // Checking to see if the argument is a pointer to something
//      if (ce->getWidth() == Context::get().getPointerWidth() &&
//          state.addressSpace.resolveOne(ce, op)) {
//        op.second->flushToConcreteStore(solver, state);
//      }
//      wordIndex += (ce->getWidth()+63)/64;
//    } else {
//      ref<Expr> arg = toUnique(state, *ai);
//      if (ConstantExpr *ce = dyn_cast<ConstantExpr>(arg)) {
//        // XXX kick toMemory functions from here
//        ce->toMemory(&args[wordIndex]);
//        wordIndex += (ce->getWidth()+63)/64;
//      } else {
//        terminateStateOnExecError(state,
//                                  "external call with symbolic argument: " +
//                                  function->getName());
//        return;
//      }
//    }
//  }
//
//  // Prepare external memory for invoking the function
//  state.addressSpace.copyOutConcretes();
//#ifndef WINDOWS
//  // Update external errno state with local state value
//  int *errno_addr = getErrnoLocation(state);
//  ObjectPair result;
//  bool resolved = state.addressSpace.resolveOne(
//          ConstantExpr::create((uint64_t)errno_addr, Expr::Int64), result);
//  if (!resolved)
//    klee_error("Could not resolve memory object for errno");
//  ref<Expr> errValueExpr = result.second->read(0, sizeof(*errno_addr) * 8);
//  ConstantExpr *errnoValue = dyn_cast<ConstantExpr>(errValueExpr);
//  if (!errnoValue) {
//    terminateStateOnExecError(state,
//                              "external call with errno value symbolic: " +
//                              function->getName());
//    return;
//  }
//
//  externalDispatcher->setLastErrno(
//          errnoValue->getZExtValue(sizeof(*errno_addr) * 8));
//#endif
//
//  if (!SuppressExternalWarnings) {
//
//    std::string TmpStr;
//    llvm::raw_string_ostream os(TmpStr);
//    os << "calling external: " << function->getName().str() << "(";
//    for (unsigned i=0; i<arguments.size(); i++) {
//      os << arguments[i];
//      if (i != arguments.size()-1)
//        os << ", ";
//    }
//
//    Thread* thread = state.getCurrentThreadReference();
//    os << ") at " << thread->pc->getSourceLocation();
//
//    if (AllExternalWarnings)
//      klee_warning("%s", os.str().c_str());
//    else
//      klee_warning_once(function, "%s", os.str().c_str());
//  }
//
//  bool success = externalDispatcher->executeCall(function, target->inst, args);
//  if (!success) {
//    terminateStateOnError(state, "failed external call: " + function->getName(),
//                          External);
//    return;
//  }
//
//  if (!state.addressSpace.copyInConcretes()) {
//    terminateStateOnError(state, "external modified read-only object",
//                          External);
//    return;
//  }
//
//#ifndef WINDOWS
//  // Update errno memory object with the errno value from the call
//  int error = externalDispatcher->getLastErrno();
//  state.addressSpace.copyInConcrete(result.first, result.second,
//                                    (uint64_t)&error);
//#endif
//
//  Type *resultType = target->inst->getType();
//  if (resultType != Type::getVoidTy(function->getContext())) {
//    ref<Expr> e = ConstantExpr::fromMemory((void*) args,
//                                           executor->getWidthForLLVMType(resultType));
//    bindLocal(target, state, e);
//  }
}

std::string ExecutionRunner::getAddressInfo(ExecutionState &state,
                                            ref<Expr> address) const{
  std::string Str;
  llvm::raw_string_ostream info(Str);
  info << "\taddress: " << address << "\n";
  uint64_t example;
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(address)) {
    example = CE->getZExtValue();
  } else {
    ref<ConstantExpr> value;
    bool success = solver->getValue(state, address, value);
    assert(success && "FIXME: Unhandled solver failure");
    (void) success;
    example = value->getZExtValue();
    info << "\texample: " << example << "\n";
    std::pair< ref<Expr>, ref<Expr> > res = solver->getRange(state, address);
    info << "\trange: [" << res.first << ", " << res.second <<"]\n";
  }

  MemoryObject hack((unsigned) example);
  MemoryMap::iterator lower = state.addressSpace.objects.upper_bound(&hack);
  info << "\tnext: ";
  if (lower==state.addressSpace.objects.end()) {
    info << "none\n";
  } else {
    const MemoryObject *mo = lower->first;
    std::string alloc_info;
    mo->getAllocInfo(alloc_info);
    info << "object at " << mo->address
         << " of size " << mo->size << "\n"
         << "\t\t" << alloc_info << "\n";
  }
  if (lower!=state.addressSpace.objects.begin()) {
    --lower;
    info << "\tprev: ";
    if (lower==state.addressSpace.objects.end()) {
      info << "none\n";
    } else {
      const MemoryObject *mo = lower->first;
      std::string alloc_info;
      mo->getAllocInfo(alloc_info);
      info << "object at " << mo->address
           << " of size " << mo->size << "\n"
           << "\t\t" << alloc_info << "\n";
    }
  }

  return info.str();
}

void ExecutionRunner::resolveExact(ExecutionState &state,
                                   ref<Expr> p,
                                   Executor::ExactResolutionList &results,
                                   const std::string &name) {
  // XXX we may want to be capping this?
  ResolutionList rl;
  state.addressSpace.resolve(state, solver, p, rl);

  ExecutionState *unbound = &state;
  for (ResolutionList::iterator it = rl.begin(), ie = rl.end();
       it != ie; ++it) {
    ref<Expr> inBounds = EqExpr::create(p, it->first->getBaseExpr());

    Executor::StatePair branches = fork(*unbound, inBounds, true);

    if (branches.first)
      results.push_back(std::make_pair(*it, branches.first));

    unbound = branches.second;
    if (!unbound) // Fork failure
      break;
  }

  if (unbound) {
    terminateStateOnError(*unbound, "memory error: invalid pointer: " + name,
                          Executor::Ptr, NULL, getAddressInfo(*unbound, p));
  }
}

void ExecutionRunner::executeAlloc(ExecutionState &state,
                                   ref<Expr> size,
                                   bool isLocal,
                                   KInstruction *target,
                                   bool zeroMemory,
                                   const ObjectState *reallocFrom) {
  // TODO: Here we should assign the ownership over the memory region to the
  //       current thread
  Thread* thread = state.getCurrentThreadReference();

  size = toUnique(state, size);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(size)) {
    const llvm::Value *allocSite = thread->prevPc->inst;
    size_t allocationAlignment = getAllocationAlignment(allocSite);
    MemoryObject *mo =
            executor->memory->allocate(CE->getZExtValue(), isLocal, /*isGlobal=*/false,
                             allocSite, allocationAlignment);
    if (!mo) {
      bindLocal(target, state,
                ConstantExpr::alloc(0, Context::get().getPointerWidth()));
    } else {
      ObjectState *os = bindObjectInState(state, mo, isLocal);
      if (zeroMemory) {
        os->initializeToZero();
      } else {
        os->initializeToRandom();
      }
      bindLocal(target, state, mo->getBaseExpr());

      if (reallocFrom) {
        unsigned count = std::min(reallocFrom->size, os->size);
        for (unsigned i=0; i<count; i++)
          os->write(i, reallocFrom->read8(i));
        state.addressSpace.unbindObject(reallocFrom->getObject());
      }
    }
  } else {
    // XXX For now we just pick a size. Ideally we would support
    // symbolic sizes fully but even if we don't it would be better to
    // "smartly" pick a value, for example we could fork and pick the
    // min and max values and perhaps some intermediate (reasonable
    // value).
    //
    // It would also be nice to recognize the case when size has
    // exactly two values and just fork (but we need to get rid of
    // return argument first). This shows up in pcre when llvm
    // collapses the size expression with a select.

    ref<ConstantExpr> example;
    bool success = solver->getValue(state, size, example);
    assert(success && "FIXME: Unhandled solver failure");
    (void) success;

    // Try and start with a small example.
    Expr::Width W = example->getWidth();
    while (example->Ugt(ConstantExpr::alloc(128, W))->isTrue()) {
      ref<ConstantExpr> tmp = example->LShr(ConstantExpr::alloc(1, W));
      bool res;
      bool success = solver->mayBeTrue(state, EqExpr::create(tmp, size), res);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      if (!res)
        break;
      example = tmp;
    }

    Executor::StatePair fixedSize = fork(state, EqExpr::create(example, size), true);

    if (fixedSize.second) {
      // Check for exactly two values
      ref<ConstantExpr> tmp;
      bool success = solver->getValue(*fixedSize.second, size, tmp);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      bool res;
      success = solver->mustBeTrue(*fixedSize.second,
                                   EqExpr::create(tmp, size),
                                   res);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      if (res) {
        executeAlloc(*fixedSize.second, tmp, isLocal,
                     target, zeroMemory, reallocFrom);
      } else {
        // See if a *really* big value is possible. If so assume
        // malloc will fail for it, so lets fork and return 0.
        Executor::StatePair hugeSize =
                fork(*fixedSize.second,
                     UltExpr::create(ConstantExpr::alloc(1U<<31, W), size),
                     true);
        if (hugeSize.first) {
          klee_message("NOTE: found huge malloc, returning 0");
          bindLocal(target, *hugeSize.first,
                    ConstantExpr::alloc(0, Context::get().getPointerWidth()));
        }

        if (hugeSize.second) {

          std::string Str;
          llvm::raw_string_ostream info(Str);
          ExprPPrinter::printOne(info, "  size expr", size);
          info << "  concretization : " << example << "\n";
          info << "  unbound example: " << tmp << "\n";
          terminateStateOnError(*hugeSize.second, "concretized symbolic size",
                                Executor::Model, NULL, info.str());
        }
      }
    }

    if (fixedSize.first) // can be zero when fork fails
      executeAlloc(*fixedSize.first, example, isLocal,
                   target, zeroMemory, reallocFrom);
  }
}

void ExecutionRunner::executeFree(ExecutionState &state,
                                  ref<Expr> address,
                                  KInstruction *target) {
  Executor::StatePair zeroPointer = fork(state, Expr::createIsZero(address), true);
  if (zeroPointer.first) {
    if (target)
      bindLocal(target, *zeroPointer.first, Expr::createPointer(0));
  }
  if (zeroPointer.second) { // address != 0
    Executor::ExactResolutionList rl;
    resolveExact(*zeroPointer.second, address, rl, "free");

    for (Executor::ExactResolutionList::iterator it = rl.begin(),
                 ie = rl.end(); it != ie; ++it) {
      const MemoryObject *mo = it->first.first;
      if (mo->isLocal) {
        terminateStateOnError(*it->second, "free of alloca", Executor::Free, NULL,
                              getAddressInfo(*it->second, address));
      } else if (mo->isGlobal) {
        terminateStateOnError(*it->second, "free of global", Executor::Free, NULL,
                              getAddressInfo(*it->second, address));
      } else {
        it->second->addressSpace.unbindObject(mo);
        if (target)
          bindLocal(target, *it->second, Expr::createPointer(0));
      }
    }
  }
}

void ExecutionRunner::executeMemoryOperation(ExecutionState &state,
                                             bool isWrite,
                                             ref<Expr> address,
                                             ref<Expr> value /* undef if read */,
                                             KInstruction *target /* undef if write */) {

  Thread* thread = state.getCurrentThreadReference();
  Expr::Width type = (isWrite ? value->getWidth() :
                      executor->getWidthForLLVMType(target->inst->getType()));
  unsigned bytes = Expr::getMinBytesForWidth(type);

//  if (SimplifySymIndices) {
//    if (!isa<ConstantExpr>(address))
//      address = state.constraints.simplifyExpr(address);
//    if (isWrite && !isa<ConstantExpr>(value))
//      value = state.constraints.simplifyExpr(value);
//  }

  // fast path: single in-bounds resolution
  ObjectPair op;
  bool success;
  solver->setTimeout(executor->coreSolverTimeout);
  if (!state.addressSpace.resolveOne(state, solver, address, op, success)) {
    address = toConstant(state, address, "resolveOne failure");
    success = state.addressSpace.resolveOne(cast<ConstantExpr>(address), op);
  }
  solver->setTimeout(0);

  if (success) {
    const MemoryObject *mo = op.first;

//    if (MaxSymArraySize && mo->size>=MaxSymArraySize) {
//      address = toConstant(state, address, "max-sym-array-size");
//    }

    ref<Expr> offset = mo->getOffsetExpr(address);

    bool inBounds;
    solver->setTimeout(executor->coreSolverTimeout);
    bool success = solver->mustBeTrue(state,
                                      mo->getBoundsCheckOffset(offset, bytes),
                                      inBounds);
    solver->setTimeout(0);
    if (!success) {
      thread->pc = thread->prevPc;
      terminateStateEarly(state, "Query timed out (bounds check).");
      return;
    }

    if (inBounds) {
      const ObjectState *os = op.second;
      if (isWrite) {
        if (os->readOnly) {
          terminateStateOnError(state, "memory error: object read only",
                                Executor::ReadOnly);
        } else {
          ObjectState *wos = state.addressSpace.getWriteable(mo, os);
          wos->write(offset, value);

          processMemoryAccess(state, mo, offset, Thread::WRITE_ACCESS);
        }
      } else {
        ref<Expr> result = os->read(offset, type);

        processMemoryAccess(state, mo, offset, Thread::READ_ACCESS);

//        if (interpreterOpts.MakeConcreteSymbolic)
//          result = replaceReadWithSymbolic(state, result);

        bindLocal(target, state, result);
      }

      return;
    }
  }

  // we are on an error path (no resolution, multiple resolution, one
  // resolution with out of bounds)

  ResolutionList rl;
  solver->setTimeout(executor->coreSolverTimeout);
  bool incomplete = state.addressSpace.resolve(state, solver, address, rl,
                                               0, executor->coreSolverTimeout);
  solver->setTimeout(0);

  // XXX there is some query wasteage here. who cares?
  ExecutionState *unbound = &state;

  for (ResolutionList::iterator i = rl.begin(), ie = rl.end(); i != ie; ++i) {
    const MemoryObject *mo = i->first;
    const ObjectState *os = i->second;
    ref<Expr> inBounds = mo->getBoundsCheckPointer(address, bytes);

    Executor::StatePair branches = fork(*unbound, inBounds, true);
    ExecutionState *bound = branches.first;

    // bound can be 0 on failure or overlapped
    if (bound) {
      if (isWrite) {
        if (os->readOnly) {
          terminateStateOnError(*bound, "memory error: object read only",
                                Executor::ReadOnly);
        } else {
          ObjectState *wos = bound->addressSpace.getWriteable(mo, os);
          ref<Expr> offset = mo->getOffsetExpr(address);
          wos->write(offset, value);

          processMemoryAccess(state, mo, offset, Thread::WRITE_ACCESS);
        }
      } else {
        ref<Expr> offset = mo->getOffsetExpr(address);
        ref<Expr> result = os->read(offset, type);
        bindLocal(target, *bound, result);

        processMemoryAccess(state, mo, offset, Thread::READ_ACCESS);
      }
    }

    unbound = branches.second;
    if (!unbound)
      break;
  }

  // XXX should we distinguish out of bounds and overlapped cases?
  if (unbound) {
    if (incomplete) {
      terminateStateEarly(*unbound, "Query timed out (resolve).");
    } else {
      terminateStateOnError(*unbound, "memory error: out of bound pointer", Executor::Ptr,
                            NULL, executor->getAddressInfo(*unbound, address));
    }
  }
}

void ExecutionRunner::branch(ExecutionState &state,
                             const std::vector< ref<Expr> > &conditions,
                             std::vector<ExecutionState*> &result) {
  TimerStatIncrementer timer(stats::forkTime);
  uint64_t N = conditions.size();
  assert(N);

  /*if (MaxForks!=~0u && stats::forks >= MaxForks) {
    unsigned next = theRNG.getInt32() % N;
    for (unsigned i=0; i<N; ++i) {
      if (i == next) {
        result.push_back(&state);
      } else {
        result.push_back(NULL);
      }
    }
  } else */ {
    //stats::forks += N-1;

    // XXX do proper balance or keep random?
    result.push_back(&state);
    for (unsigned i=1; i<N; ++i) {
      ExecutionState *es = result[theRNG.getInt32() % i];
      ExecutionState *ns = es->branch();
      addedStates.push_back(ns);
      result.push_back(ns);
      es->ptreeNode->data = 0;
      std::pair<PTree::Node*,PTree::Node*> res =
              processTree->split(es->ptreeNode, ns, es);
      ns->ptreeNode = res.first;
      es->ptreeNode = res.second;
    }
  }

  // If necessary redistribute seeds to match conditions, killing
  // states if necessary due to OnlyReplaySeeds (inefficient but
  // simple).

//  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it =
//          seedMap.find(&state);
//  if (it != seedMap.end()) {
//    std::vector<SeedInfo> seeds = it->second;
//    seedMap.erase(it);
//
//    // Assume each seed only satisfies one condition (necessarily true
//    // when conditions are mutually exclusive and their conjunction is
//    // a tautology).
//    for (std::vector<SeedInfo>::iterator siit = seeds.begin(),
//                 siie = seeds.end(); siit != siie; ++siit) {
//      unsigned i;
//      for (i=0; i<N; ++i) {
//        ref<ConstantExpr> res;
//        bool success =
//                solver->getValue(state, siit->assignment.evaluate(conditions[i]),
//                                 res);
//        assert(success && "FIXME: Unhandled solver failure");
//        (void) success;
//        if (res->isTrue())
//          break;
//      }
//
//      // If we didn't find a satisfying condition randomly pick one
//      // (the seed will be patched).
//      if (i==N)
//        i = theRNG.getInt32() % N;
//
//      // Extra check in case we're replaying seeds with a max-fork
//      if (result[i])
//        seedMap[result[i]].push_back(*siit);
//    }
//
//    if (OnlyReplaySeeds) {
//      for (unsigned i=0; i<N; ++i) {
//        if (result[i] && !seedMap.count(result[i])) {
//          terminateState(*result[i]);
//          result[i] = NULL;
//        }
//      }
//    }
//  }

  for (unsigned i=0; i<N; ++i)
    if (result[i])
      addConstraint(*result[i], conditions[i]);
}

Executor::StatePair
ExecutionRunner::fork(ExecutionState &current, ref<Expr> condition, bool isInternal) {
  Solver::Validity res;
//  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it =
//          seedMap.find(&current);
//  bool isSeeding = it != seedMap.end();
//
//  if (!isSeeding && !isa<ConstantExpr>(condition) &&
//      (MaxStaticForkPct!=1. || MaxStaticSolvePct != 1. ||
//       MaxStaticCPForkPct!=1. || MaxStaticCPSolvePct != 1.) &&
//      statsTracker->elapsed() > 60.) {
//    StatisticManager &sm = *theStatisticManager;
//
//    // FIXME: Just assume that we the call should return the current thread, but what is the correct behavior
//    Thread* thread = current.getCurrentThreadReference();
//    CallPathNode *cpn = thread->stack.back().callPathNode;
//
//    if ((MaxStaticForkPct<1. &&
//         sm.getIndexedValue(stats::forks, sm.getIndex()) >
//         stats::forks*MaxStaticForkPct) ||
//        (MaxStaticCPForkPct<1. &&
//         cpn && (cpn->statistics.getValue(stats::forks) >
//                 stats::forks*MaxStaticCPForkPct)) ||
//        (MaxStaticSolvePct<1 &&
//         sm.getIndexedValue(stats::solverTime, sm.getIndex()) >
//         stats::solverTime*MaxStaticSolvePct) ||
//        (MaxStaticCPForkPct<1. &&
//         cpn && (cpn->statistics.getValue(stats::solverTime) >
//                 stats::solverTime*MaxStaticCPSolvePct))) {
//      ref<ConstantExpr> value;
//      bool success = solver->getValue(current, condition, value);
//      assert(success && "FIXME: Unhandled solver failure");
//      (void) success;
//      addConstraint(current, EqExpr::create(value, condition));
//      condition = value;
//    }
//  }

  double timeout = executor->coreSolverTimeout;
//  if (isSeeding)
//    timeout *= it->second.size();
  solver->setTimeout(timeout);
  bool success = solver->evaluate(current, condition, res);
  solver->setTimeout(0);
  if (!success) {
    // Since we were unsuccessful, restore the previous program counter for the current thread
    Thread* thread = current.getCurrentThreadReference();
    thread->pc = thread->prevPc;

    terminateStateEarly(current, "Query timed out (fork).");
    return Executor::StatePair(0, 0);
  }

//  if (!isSeeding) {
//    if (!replayPath || isInternal) {
//      if (res == Solver::Unknown) {
//        assert(!replayKTest && "in replay mode, only one branch can be true.");
//
//        if ((MaxMemoryInhibit && atMemoryLimit) ||
//            current.forkDisabled ||
//            inhibitForking ||
//            (MaxForks != ~0u && stats::forks >= MaxForks)) {
//
//          if (MaxMemoryInhibit && atMemoryLimit)
//            klee_warning_once(0, "skipping fork (memory cap exceeded)");
//          else if (current.forkDisabled)
//            klee_warning_once(0, "skipping fork (fork disabled on current path)");
//          else if (inhibitForking)
//            klee_warning_once(0, "skipping fork (fork disabled globally)");
//          else
//            klee_warning_once(0, "skipping fork (max-forks reached)");
//
//          TimerStatIncrementer timer(stats::forkTime);
//          if (theRNG.getBool()) {
//            addConstraint(current, condition);
//            res = Solver::True;
//          } else {
//            addConstraint(current, Expr::createIsZero(condition));
//            res = Solver::False;
//          }
//        }
//      }
//    } else {
//      assert(replayPosition < replayPath->size() &&
//             "ran out of branches in replay path mode");
//      bool branch = (*replayPath)[replayPosition++];
//
//      if (res == Solver::True) {
//        assert(branch && "hit invalid branch in replay path mode");
//      } else if (res == Solver::False) {
//        assert(!branch && "hit invalid branch in replay path mode");
//      } else {
//        // add constraints
//        if (branch) {
//          res = Solver::True;
//          addConstraint(current, condition);
//        } else {
//          res = Solver::False;
//          addConstraint(current, Expr::createIsZero(condition));
//        }
//      }
//    }
//  }

  // Fix branch in only-replay-seed mode, if we don't have both true
  // and false seeds.
//  if (isSeeding &&
//      (current.forkDisabled || OnlyReplaySeeds) &&
//      res == Solver::Unknown) {
//    bool trueSeed=false, falseSeed=false;
//    // Is seed extension still ok here?
//    for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
//                 siie = it->second.end(); siit != siie; ++siit) {
//      ref<ConstantExpr> res;
//      bool success =
//              solver->getValue(current, siit->assignment.evaluate(condition), res);
//      assert(success && "FIXME: Unhandled solver failure");
//      (void) success;
//      if (res->isTrue()) {
//        trueSeed = true;
//      } else {
//        falseSeed = true;
//      }
//      if (trueSeed && falseSeed)
//        break;
//    }
//    if (!(trueSeed && falseSeed)) {
//      assert(trueSeed || falseSeed);
//
//      res = trueSeed ? Solver::True : Solver::False;
//      addConstraint(current, trueSeed ? condition : Expr::createIsZero(condition));
//    }
//  }


  // XXX - even if the constraint is provable one way or the other we
  // can probably benefit by adding this constraint and allowing it to
  // reduce the other constraints. For example, if we do a binary
  // search on a particular value, and then see a comparison against
  // the value it has been fixed at, we should take this as a nice
  // hint to just use the single constraint instead of all the binary
  // search ones. If that makes sense.
  if (res==Solver::True) {
    if (!isInternal) {
//      if (pathWriter) {
//        current.pathOS << "1";
//      }
    }

    return Executor::StatePair(&current, 0);
  } else if (res==Solver::False) {
    if (!isInternal) {
//      if (pathWriter) {
//        current.pathOS << "0";
//      }
    }

    return Executor::StatePair(0, &current);
  } else {
    TimerStatIncrementer timer(stats::forkTime);
    ExecutionState *falseState, *trueState = &current;

    // ++stats::forks;

    falseState = trueState->branch();
    addedStates.push_back(falseState);

//    if (it != seedMap.end()) {
//      std::vector<SeedInfo> seeds = it->second;
//      it->second.clear();
//      std::vector<SeedInfo> &trueSeeds = seedMap[trueState];
//      std::vector<SeedInfo> &falseSeeds = seedMap[falseState];
//      for (std::vector<SeedInfo>::iterator siit = seeds.begin(),
//                   siie = seeds.end(); siit != siie; ++siit) {
//        ref<ConstantExpr> res;
//        bool success =
//                solver->getValue(current, siit->assignment.evaluate(condition), res);
//        assert(success && "FIXME: Unhandled solver failure");
//        (void) success;
//        if (res->isTrue()) {
//          trueSeeds.push_back(*siit);
//        } else {
//          falseSeeds.push_back(*siit);
//        }
//      }
//
//      bool swapInfo = false;
//      if (trueSeeds.empty()) {
//        if (&current == trueState) swapInfo = true;
//        seedMap.erase(trueState);
//      }
//      if (falseSeeds.empty()) {
//        if (&current == falseState) swapInfo = true;
//        seedMap.erase(falseState);
//      }
//      if (swapInfo) {
//        std::swap(trueState->coveredNew, falseState->coveredNew);
//        std::swap(trueState->coveredLines, falseState->coveredLines);
//      }
//    }

    current.ptreeNode->data = 0;
    std::pair<PTree::Node*, PTree::Node*> res =
            processTree->split(current.ptreeNode, falseState, trueState);
    falseState->ptreeNode = res.first;
    trueState->ptreeNode = res.second;

//    if (pathWriter) {
//      // Need to update the pathOS.id field of falseState, otherwise the same id
//      // is used for both falseState and trueState.
//      falseState->pathOS = pathWriter->open(current.pathOS);
//      if (!isInternal) {
//        trueState->pathOS << "1";
//        falseState->pathOS << "0";
//      }
//    }
//    if (symPathWriter) {
//      falseState->symPathOS = symPathWriter->open(current.symPathOS);
//      if (!isInternal) {
//        trueState->symPathOS << "1";
//        falseState->symPathOS << "0";
//      }
//    }

    addConstraint(*trueState, condition);
    addConstraint(*falseState, Expr::createIsZero(condition));

    // Kinda gross, do we even really still want this option?
//    if (MaxDepth && MaxDepth<=trueState->depth) {
//      terminateStateEarly(*trueState, "max-depth exceeded.");
//      terminateStateEarly(*falseState, "max-depth exceeded.");
//      return Executor::StatePair(0, 0);
//    }

    return Executor::StatePair(trueState, falseState);
  }
}

void ExecutionRunner::executeGetValue(ExecutionState &state,
                                      ref<Expr> e,
                                      KInstruction *target) {
  e = state.constraints.simplifyExpr(e);
//  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it =
//          seedMap.find(&state);
  if (/*it==seedMap.end() || */isa<ConstantExpr>(e)) {
    ref<ConstantExpr> value;
    bool success = solver->getValue(state, e, value);
    assert(success && "FIXME: Unhandled solver failure");
    (void) success;
    bindLocal(target, state, value);
  } /* else {
    std::set< ref<Expr> > values;
    for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
                 siie = it->second.end(); siit != siie; ++siit) {
      ref<ConstantExpr> value;
      bool success =
              solver->getValue(state, siit->assignment.evaluate(e), value);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      values.insert(value);
    }

    std::vector< ref<Expr> > conditions;
    for (std::set< ref<Expr> >::iterator vit = values.begin(),
                 vie = values.end(); vit != vie; ++vit)
      conditions.push_back(EqExpr::create(e, *vit));

    std::vector<ExecutionState*> branches;
    branch(state, conditions, branches);

    std::vector<ExecutionState*>::iterator bit = branches.begin();
    for (std::set< ref<Expr> >::iterator vit = values.begin(),
                 vie = values.end(); vit != vie; ++vit) {
      ExecutionState *es = *bit;
      if (es)
        bindLocal(target, *es, *vit);
      ++bit;
    }
  }*/
}

size_t ExecutionRunner::getAllocationAlignment(const llvm::Value *allocSite) const {
  // FIXME: 8 was the previous default. We shouldn't hard code this
  // and should fetch the default from elsewhere.
  const size_t forcedAlignment = 8;
  size_t alignment = 0;
  llvm::Type *type = NULL;
  std::string allocationSiteName(allocSite->getName().str());
  if (const GlobalValue *GV = dyn_cast<GlobalValue>(allocSite)) {
    alignment = GV->getAlignment();
    if (const GlobalVariable *globalVar = dyn_cast<GlobalVariable>(GV)) {
      // All GlobalVariables's have pointer type
      llvm::PointerType *ptrType =
              dyn_cast<llvm::PointerType>(globalVar->getType());
      assert(ptrType && "globalVar's type is not a pointer");
      type = ptrType->getElementType();
    } else {
      type = GV->getType();
    }
  } else if (const AllocaInst *AI = dyn_cast<AllocaInst>(allocSite)) {
    alignment = AI->getAlignment();
    type = AI->getAllocatedType();
  } else if (isa<InvokeInst>(allocSite) || isa<CallInst>(allocSite)) {
    // FIXME: Model the semantics of the call to use the right alignment
    llvm::Value *allocSiteNonConst = const_cast<llvm::Value *>(allocSite);
    const CallSite cs = (isa<InvokeInst>(allocSiteNonConst)
                         ? CallSite(cast<InvokeInst>(allocSiteNonConst))
                         : CallSite(cast<CallInst>(allocSiteNonConst)));
    llvm::Function *fn =
            klee::getDirectCallTarget(cs, /*moduleIsFullyLinked=*/true);
    if (fn)
      allocationSiteName = fn->getName().str();

    klee_warning_once(fn != NULL ? fn : allocSite,
                      "Alignment of memory from call \"%s\" is not "
                      "modelled. Using alignment of %zu.",
                      allocationSiteName.c_str(), forcedAlignment);
    alignment = forcedAlignment;
  } else {
    llvm_unreachable("Unhandled allocation site");
  }

  if (alignment == 0) {
    assert(type != NULL);
    // No specified alignment. Get the alignment for the type.
    if (type->isSized()) {
      alignment = executor->kmodule->targetData->getPrefTypeAlignment(type);
    } else {
      klee_warning_once(allocSite, "Cannot determine memory alignment for "
                                   "\"%s\". Using alignment of %zu.",
                        allocationSiteName.c_str(), forcedAlignment);
      alignment = forcedAlignment;
    }
  }

  // Currently we require alignment be a power of 2
  if (!bits64::isPowerOfTwo(alignment)) {
    klee_warning_once(allocSite, "Alignment of %zu requested for %s but this "
                                 "not supported. Using alignment of %zu",
                      alignment, allocSite->getName().str().c_str(),
                      forcedAlignment);
    alignment = forcedAlignment;
  }
  assert(bits64::isPowerOfTwo(alignment) &&
         "Returned alignment must be a power of two");
  return alignment;
}

void ExecutionRunner::executeMakeSymbolic(ExecutionState &state,
                                          const MemoryObject *mo,
                                          const std::string &name) {
  // Create a new object state for the memory object (instead of a copy).
  /*if (!replayKTest)*/ {
    // Find a unique name for this array.  First try the original name,
    // or if that fails try adding a unique identifier.
    unsigned id = 0;
    std::string uniqueName = name;
    while (!state.arrayNames.insert(uniqueName).second) {
      uniqueName = name + "_" + llvm::utostr(++id);
    }
    const Array *array = executor->arrayCache.CreateArray(uniqueName, mo->size);
    bindObjectInState(state, mo, false, array);
    state.addSymbolic(mo, array);

//    std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it =
//            seedMap.find(&state);
//    if (it!=seedMap.end()) { // In seed mode we need to add this as a
//      // binding.
//      for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
//                   siie = it->second.end(); siit != siie; ++siit) {
//        SeedInfo &si = *siit;
//        KTestObject *obj = si.getNextInput(mo, NamedSeedMatching);
//
//        if (!obj) {
//          if (ZeroSeedExtension) {
//            std::vector<unsigned char> &values = si.assignment.bindings[array];
//            values = std::vector<unsigned char>(mo->size, '\0');
//          } else if (!AllowSeedExtension) {
//            terminateStateOnError(state, "ran out of inputs during seeding",
//                                  User);
//            break;
//          }
//        } else {
//          if (obj->numBytes != mo->size &&
//              ((!(AllowSeedExtension || ZeroSeedExtension)
//                && obj->numBytes < mo->size) ||
//               (!AllowSeedTruncation && obj->numBytes > mo->size))) {
//            std::stringstream msg;
//            msg << "replace size mismatch: "
//                << mo->name << "[" << mo->size << "]"
//                << " vs " << obj->name << "[" << obj->numBytes << "]"
//                << " in test\n";
//
//            terminateStateOnError(state, msg.str(), User);
//            break;
//          } else {
//            std::vector<unsigned char> &values = si.assignment.bindings[array];
//            values.insert(values.begin(), obj->bytes,
//                          obj->bytes + std::min(obj->numBytes, mo->size));
//            if (ZeroSeedExtension) {
//              for (unsigned i=obj->numBytes; i<mo->size; ++i)
//                values.push_back('\0');
//            }
//          }
//        }
//      }
//    }
  } // else {
//    ObjectState *os = bindObjectInState(state, mo, false);
//    if (replayPosition >= replayKTest->numObjects) {
//      terminateStateOnError(state, "replay count mismatch", User);
//    } else {
//      KTestObject *obj = &replayKTest->objects[replayPosition++];
//      if (obj->numBytes != mo->size) {
//        terminateStateOnError(state, "replay size mismatch", User);
//      } else {
//        for (unsigned i=0; i<mo->size; i++)
//          os->write8(i, obj->bytes[i]);
//      }
//    }
//  }
}

KFunction* ExecutionRunner::obtainFunctionFromExpression(ref<Expr> address) {
  for (auto f : executor->kmodule->functions) {
    ref<Expr> addr = Expr::createPointer((uint64_t) (void*) f->function);

    if (addr == address) {
      return f;
    }
  }

  return nullptr;
}

void ExecutionRunner::createThread(ExecutionState &state, Thread::ThreadId tid,
                            ref<Expr> startRoutine, ref<Expr> arg) {
  KFunction *kf = obtainFunctionFromExpression(startRoutine);
  assert(kf && "could not obtain the start routine");

  Thread* thread = state.createThread(tid, kf);
  StackFrame* threadStartFrame = &thread->stack.back();

  threadStartFrame->locals[kf->getArgRegister(0)].value = arg;

  //if (statsTracker)
  //  statsTracker->framePushed(&thread->stack.back(), 0);

  scheduleThreads(state);
}

void ExecutionRunner::sleepThread(ExecutionState &state) {
  state.sleepCurrentThread();
  scheduleThreads(state);
}

void ExecutionRunner::wakeUpThread(ExecutionState &state, Thread::ThreadId tid) {
  state.wakeUpThread(tid);
  scheduleThreads(state);
}

void ExecutionRunner::preemptThread(ExecutionState &state) {
  state.preemptCurrentThread();
  scheduleThreads(state);
}

void ExecutionRunner::exitThread(ExecutionState &state) {
  state.exitThread(state.getCurrentThreadReference()->getThreadId());
  scheduleThreads(state);
}

void ExecutionRunner::toggleThreadScheduling(ExecutionState &state, bool enabled) {
  state.threadSchedulingEnabled = enabled;
}

bool ExecutionRunner::processMemoryAccess(ExecutionState &state, const MemoryObject* mo, ref<Expr> offset, uint8_t type) {
  Thread* curThread = state.getCurrentThreadReference();
  Thread::ThreadId curThreadId = curThread->getThreadId();

  bool isRead = (type & Thread::Thread::READ_ACCESS);

  bool isThreadSafeMemAccess = true;
  std::vector<Thread::MemoryAccess> possibleCandidates;

  // Phase 1: Try to find a unsafe interference based on a constant
  //          offset first. This is cheaper. But record possible
  //          candidates on the go as well
  for (auto& threadsIt : state.threads) {
    Thread* thread = &threadsIt.second;

    if (thread->getThreadId() == curThreadId) {
      // Memory accesses of the current thread are safe by definition
      continue;
    }

    auto accesses = thread->syncPhaseAccesses.find(mo);
    if (accesses == thread->syncPhaseAccesses.end()) {
      // No access to that memory region from this thread
      continue;
    }

    for (auto& access : accesses->second) {
      // There is one safe memory access pattern:
      // read + read -> so we can skip these
      bool recIsRead = (access.type & Thread::READ_ACCESS);
      if (isRead && recIsRead) {
        continue;
      }

      if (access.offset == offset) {
        isThreadSafeMemAccess = false;
        continue;
      }

      // So the offset Expr are not the same but we maybe can get
      // a result that is the same
      // But: filter out Const + Const pairs
      if (isa<ConstantExpr>(offset) && isa<ConstantExpr>(access.offset)) {
        continue;
      }

      // So add it to the ones we want to test
      possibleCandidates.push_back(access);
    }

    // If we already found a unsafe access then safe computation time
    // and return right away
    if (!isThreadSafeMemAccess) {
      break;
    }
  }

  // Phase 2: If we did not find a const unsafe offset, then
  //          test all possible offset candidates
  if (isThreadSafeMemAccess && !possibleCandidates.empty()) {
    // Now test every one of them with the solver if they can point to the same
    // offset

    for (auto& candidateIt : possibleCandidates) {
      ref<Expr> condition = NeExpr::create(offset, candidateIt.offset);

      solver->setTimeout(executor->coreSolverTimeout);
      bool alwaysDifferent = true;
      bool solverSuccessful = solver->mustBeTrue(state, condition, alwaysDifferent);
      solver->setTimeout(0);

      if (!solverSuccessful) {
        klee_warning("Solver could not complete query for offset; Skipping possible unsafe mem access test");
        continue;
      }

      if (!alwaysDifferent) {
        // Now we know that both can be equal!

        // TODO: We should probably fork the state here:
        // -> we generate a error case
        // -> test what happens without an error case (force offsets to be unequal)

        // the error is that both offsets point to the same memory region so go
        // ahead and add the constraint that they are equal
        addConstraint(state, EqExpr::create(offset, candidateIt.offset));

        isThreadSafeMemAccess = false;
        break;
      } else {
        // We were not successful, so go ahead and add the constraint
        // that they are always unequal
        addConstraint(state, condition);
      }
    }
  }

  if (!isThreadSafeMemAccess) {
    exitWithUnsafeMemAccess(state, mo);
  } else {
    // This is a safe memory access, we can go ahead and
    // track it for the next states
    state.trackMemoryAccess(mo, offset, type);
  }

  return isThreadSafeMemAccess;
}

void ExecutionRunner::exitWithUnsafeMemAccess(ExecutionState &state, const MemoryObject* mo) {
  std::string TmpStr;
  llvm::raw_string_ostream os(TmpStr);
  os << "Unsafe access to memory from multiple threads\nAffected memory: ";

  std::string memInfo;
  mo->getAllocInfo(memInfo);
  os << memInfo << "\n";

  terminateStateOnError(state, "thread unsafe memory access",
                        Executor::UnsafeMemoryAccess, nullptr, os.str());
}

void ExecutionRunner::exitWithDeadlock(ExecutionState &state) {
  std::string TmpStr;
  llvm::raw_string_ostream os(TmpStr);
  os << "Deadlock in scheduling with ";
  state.dumpSchedulingInfo(os);
  os << "\nTraces:\n";
  state.dumpAllThreadStacks(os);

  terminateStateOnError(state, "all non-exited threads are sleeping",
                        Executor::Deadlock, nullptr, os.str());
}

void ExecutionRunner::scheduleThreads(ExecutionState &state) {
  // The first thing we have to test is, if we can actually try
  // to schedule a thread now; (test if scheduling enabled)
  if (!state.threadSchedulingEnabled) {
    // So now we have to check if the current thread may be scheduled
    // or if we have a deadlock

    Thread* curThread = state.getCurrentThreadReference();
    if (curThread->state == Thread::ThreadState::SLEEPING) {
      exitWithDeadlock(state);
      return;
    }

    if (curThread->state != Thread::ThreadState::EXITED) {
      // So we can actually reschedule the current thread
      // but make sure that the thread is marked as RUNNABLE
      curThread->state = Thread::ThreadState::RUNNABLE;
      state.setCurrentScheduledThread(curThread->getThreadId());
      return;
    }

    // So how do we proceed here? For now just let everything continue normally
    // this will schedule another thread
  }

  std::vector<Thread::ThreadId> runnable = state.calculateRunnableThreads();

  if (runnable.empty()) {
    // So all have reached the current sync point, move to the new one
    bool oneNowRunnable = state.moveToNewSyncPhase();
    if (oneNowRunnable) {
      runnable = state.calculateRunnableThreads();
    }
  }

  if (runnable.empty()) {
    bool allExited = true;

    for (auto& threadIt : state.threads) {
      if (threadIt.second.state != Thread::ThreadState::EXITED) {
        allExited = false;
      }
    }

    if (allExited) {
      terminateStateOnExit(state);
    } else {
      exitWithDeadlock(state);
    }

    // Make sure that we do not change the current state
    return;
  } else if (runnable.size() == 1 || (!ForkOnThreadScheduling && !ForkOnStatement) || state.forkDisabled) {
    // The easiest possible schedule
    state.setCurrentScheduledThread(runnable.front());
    return;
  }

  // Now we have to branch for each possible thread scheduling
  // this basically means we have to add (runnable.size() - 1) more states
  // TODO: maybe we can also compare the stacks of the threads and can form
  //       groups of 'equivalent' threads. Based on them we then could only
  //       add one thread per group

  // stats::forks += runnable.size() - 1;

  for (size_t i = 1; i < runnable.size(); ++i) {
    ExecutionState* ns = state.branch();
    addedStates.push_back(ns);
    ns->setCurrentScheduledThread(runnable[i]);

    state.ptreeNode->data = nullptr;
    auto res = processTree->split(state.ptreeNode, ns, &state);
    ns->ptreeNode = res.first;
    state.ptreeNode = res.second;

//    if (pathWriter) {
//      ns->pathOS = pathWriter->open(state.pathOS);
//    }
//
//    if (symPathWriter) {
//      ns->symPathOS = symPathWriter->open(state.symPathOS);
//    }
  }

  // We need to push it to the back
  state.setCurrentScheduledThread(runnable.front());
  state.hasScheduledThreads = true;
}

// TODO: For now just pass down to the executor

void ExecutionRunner::terminateState(ExecutionState &state) {
  executor->terminateState(state);
}

void ExecutionRunner::terminateStateEarly(ExecutionState &state, const llvm::Twine &message) {
  executor->terminateStateEarly(state, message);
}

void ExecutionRunner::terminateStateOnExit(ExecutionState &state) {
  executor->terminateStateOnExit(state);
}

void ExecutionRunner::terminateStateOnError(ExecutionState &state, const llvm::Twine &message,
                           enum Executor::TerminateReason termReason,
                           const char *suffix,
                           const llvm::Twine &longMessage ) {
   executor->terminateStateOnError(state, message, termReason, suffix, longMessage);
}

/*###################### GRAVEYARD ###################*/

void ExecutionRunner::doImpliedValueConcretization(ExecutionState &state,
                                            ref<Expr> e,
                                            ref<ConstantExpr> value) {
  abort(); // FIXME: Broken until we sort out how to do the write back.

//  if (DebugCheckForImpliedValues)
//    ImpliedValue::checkForImpliedValues(solver->solver, e, value);
//
//  ImpliedValueList results;
//  ImpliedValue::getImpliedValues(e, value, results);
//  for (ImpliedValueList::iterator it = results.begin(), ie = results.end();
//       it != ie; ++it) {
//    ReadExpr *re = it->first.get();
//
//    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(re->index)) {
//      // FIXME: This is the sole remaining usage of the Array object
//      // variable. Kill me.
//      const MemoryObject *mo = 0; //re->updates.root->object;
//      const ObjectState *os = state.addressSpace.findObject(mo);
//
//      if (!os) {
//        // object has been free'd, no need to concretize (although as
//        // in other cases we would like to concretize the outstanding
//        // reads, but we have no facility for that yet)
//      } else {
//        assert(!os->readOnly &&
//               "not possible? read only object with static read?");
//        ObjectState *wos = state.addressSpace.getWriteable(mo, os);
//        wos->write(CE, it->second);
//      }
//    }
//  }
}