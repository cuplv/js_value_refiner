package edu.colorado.plv.js_value_refiner

import dk.brics.tajs.analysis.nativeobjects.ECMAScriptObjects
import dk.brics.tajs.flowgraph.{AbstractNode, Function}
import dk.brics.tajs.flowgraph.jsnodes.ConstantNode.Type
import dk.brics.tajs.flowgraph.jsnodes._
import dk.brics.tajs.flowgraph.jsnodes.UnaryOperatorNode.{Op => UnOp}
import dk.brics.tajs.lattice.ObjectLabel.Kind
import dk.brics.tajs.lattice.{ObjectLabel, State, Value}
import dk.brics.tajs.util.AnalysisException
import edu.colorado.plv.js_value_refiner.constraint._
import edu.colorado.plv.js_value_refiner.memory.{ProgramVar, Register, Variable}
import edu.colorado.plv.value_refiner.AbstractValue
import forwards_backwards_api.memory.Property
import forwards_backwards_api.{Forwards, ProgramLocation, Properties}

import scala.collection.JavaConversions._
import scala.collection.immutable.Stack
import scala.language.postfixOps
import scala.util.{Failure, Success, Try}

class BackwardsTransfer(forwards : Forwards) {
  /**
    * Apply node transfer functions across an entire Basic Block
    *
    * @return Set of resulting [[DisjunctState]]s
    */
  def transfer(ds: DisjunctState): Set[DisjunctState] = {
    if(ds.block.getLastNode.isInstanceOf[BeginLoopNode] &&
       ds.block.getFirstNode == ds.loc.getNode &&
       forwards.getPredecessors(ds.loc).size == 2) {
      val preds = forwards.getPredecessors(ds.loc)
      if(ds.containingLoopInitialStores.nonEmpty && ds.containingLoopInitialStores.head._1.getNode == ds.loc.getNode) {
        // We've already passed through this loop once, continue above through the loop init
        val loop_init_pred = preds.find{_.getNode.getBlock.getIndex < ds.block.getIndex}.get
        val initialStore = ds.containingLoopInitialStores.head._2
        val stores = loop_init_pred.getNode match {
          case _:IfNode => ds.stores map trackConditional(loop_init_pred,loop_init_pred.getNode.asInstanceOf[IfNode].getSuccTrue == ds.loc.getNode.getBlock)
          case _ => ds.stores
        }
        Set(DisjunctState(loop_init_pred, storeTransfer(stores, ds.loc) flatMap initialStore.join toSet, ds.callStack, ds.containingLoopInitialStores.pop))
      } else {
        // We haven't traversed the loop yet, go to the exit of the loop body
        preds.find{_.getNode.getBlock.getIndex > ds.block.getIndex} match { // NOTE: The loop body are not necessarily a predecessor to the beginLoop node
          case Some(loop_body_pred) =>
            val stores = loop_body_pred.getNode match {
              case _:IfNode => ds.stores map trackConditional(loop_body_pred,loop_body_pred.getNode.asInstanceOf[IfNode].getSuccTrue == ds.loc.getNode.getBlock)
              case _ => ds.stores
            }
            stores map { st =>
              DisjunctState (loop_body_pred, storeTransfer (st::Nil, ds.loc).toSet, ds.callStack, ds.containingLoopInitialStores push (ds.loc -> st) )
            }
          case None => preds.flatMap(p => { // If no exit node is predecessor to the beginLoopNode, just traverse backwards to all predecessors
            ds.stores.map(st => {
              DisjunctState (p, storeTransfer (st::Nil, ds.loc).toSet, ds.callStack, ds.containingLoopInitialStores push (ds.loc -> st) )
            })
          }).toSet
        }
      }
    } else if (ds.loc.getNode.isInstanceOf[BeginForInNode]) { //If ds.loc is the start of a for-in loop
      val (loopRepeatPreds, loopBeginPreds) = forwards.getPredecessors(ds.loc).partition { pred => ds.loc.getNode.asInstanceOf[BeginForInNode].getEndNodes.contains(pred.getNode) }
      ds.stores flatMap { store =>
        val lc = store.loopConstraints.find {
          _.loopHead == ds.loc.getNode
        }.get
        if (lc.next.isDefined && loopRepeatPreds.nonEmpty) {
          loopRepeatPreds flatMap { pred =>
            Try(pred.getContext.getSpecialRegisters.get(lc.loopHead.getPropertyListRegister).getStr) match {
              case Success(specialRegVal) if specialRegVal == lc.next.get.propValue =>
              Some(DisjunctState(pred, Set(store.dropConstraint(lc).addConstraint(lc.next.get)), ds.callStack, ds.containingLoopInitialStores))
              case x => None
            }
          }
        } else {
          loopBeginPreds map { pred => DisjunctState(pred, storeTransfer(store::Nil, ds.loc).toSet, ds.callStack, ds.containingLoopInitialStores) }
        }
      }
    } else {
      val preds: Iterable[ProgramLocation] = ds.loc.getNode match {
        //Skip property-iterator bookkeeping by jumping from NextPropertyNode directly to corresponding BeginForInNode
        case n: NextPropertyNode =>
          val pred1 = forwards.getPredecessors(ds.loc)
          require(pred1.size == 1)
          val pred2 = forwards.getPredecessors(pred1.head)
          require(pred2.size == 1)
          forwards getPredecessors pred2.head
        case _ => forwards.getPredecessors(ds.loc)
      }
      val res_stores = storeTransfer(ds.stores, ds.loc).toSet

      if (res_stores.isEmpty) Set()
      else if (preds.nonEmpty) {
        preds flatMap { pred => pred.getNode match {
            case call: CallNode =>
              val intraAppCallResults: List[DisjunctState] = if (call.isConstructorCall)
                doConstructorExit(pred, res_stores, ds.callStack, ds.containingLoopInitialStores) toList
              else
                doDispatchOrInvokeExit(pred, res_stores, ds.callStack, ds.containingLoopInitialStores) toList
              val nativeCallResults: Set[AbstrStore] = try { Natives(pred, res_stores, forwards) } catch { case e:AnalysisException => Set() }
              DisjunctState(pred, nativeCallResults, ds.callStack, ds.containingLoopInitialStores) :: intraAppCallResults
            case i: IfNode =>
              val condReg = Register(i.getConditionRegister, pred)
              val branch = i.getSuccTrue == ds.loc.getNode.getBlock
              Some(DisjunctState(pred, res_stores map trackConditional(pred,branch), ds.callStack, ds.containingLoopInitialStores
              ))
            case e: EndForInNode =>
              //EndForInNode is either an exit of the loop, or a return to the loop head.  By design, this will never be called on a return to the loop head.
              // For all for-in loops, pred^3(exit_location)==singleton(begin_location)
              val beginLoc = forwards.getPredecessors(forwards.getPredecessors(forwards.getPredecessors(pred).head).head).head
              assert(beginLoc.getNode == e.getBeginNode)

              forwards.getPredecessors(beginLoc) filter { pred =>
                (e.getBeginNode.getEndNodes contains pred.getNode) && {
                  val beginSpecialRegs: Map[Integer, Value] = beginLoc.getContext.getSpecialRegisters match {case null => Map(); case x => Map(x.iterator.toSeq: _*)}
                  val  predSpecialRegs: Map[Integer, Value] =     pred.getContext.getSpecialRegisters match {case null => Map(); case x => Map(x.iterator.toSeq: _*)}
                  beginSpecialRegs forall { s => predSpecialRegs.get(s._1) == Some(s._2) }
                }
              } map { pred =>
                DisjunctState(pred,BackwardsTransfer.makeStoresWithLoopCtx(beginLoc, forwards,res_stores), ds.callStack, ds.containingLoopInitialStores)
              }
            case _ => Some(DisjunctState(pred, res_stores, ds.callStack, ds.containingLoopInitialStores))
          }
        } toSet
      } else {
        // preds are empty.  Return to procedure call
        doCallEntry(ds.loc, res_stores, ds.callStack, ds.containingLoopInitialStores)
      }
    }
  }

  /** Backwards transfer functions over TAJS IR Nodes. */
  private def storeTransfer(stores: Iterable[AbstrStore], loc: ProgramLocation): Iterable[AbstrStore] = {
    val res = try nodeTransferFns(stores, loc) map {
      _.canonicalize(forwards, loc)
    } filter {
      _.isSatisfiable(forwards, loc)
    } catch {case e : AnalysisException => Nil}
    debug(s"\n${stores mkString "\n"}\n\t" +
          loc.getNode.getIndex + ":" + loc.getNode +
          (if (res.isEmpty) Console.RED + " REFUTED" + Console.RESET
           else s"\n${res mkString "\n"}\n"))
    res
  }



  /** jump from a dispatch CallNode to all of its callees, scoping out locals as needed, binding the return value, and binding the call's receiver to `this` within each callee */
  def doDispatchOrInvokeExit(call: ProgramLocation, stores: Iterable[AbstrStore], stack: Stack[(ProgramLocation,Iterable[Constraint])], loopCtx : Stack[(ProgramLocation,AbstrStore)]): Iterable[DisjunctState] = {
    val resReg = Register(call.getNode.asInstanceOf[CallNode].getResultRegister,  call)

    //Given an abstract store, bind the function instance of this call to a symbolic variable, returning the resulting store and the bound symbolic variable.
    def bindFnInstance(st : AbstrStore): (AbstrStore, SymbolicVar) = {
      val callNode = call.getNode.asInstanceOf[CallNode]
      if(callNode.getFunctionRegister >= 0) {
        val st_with_binding = st.withLocalBinding(Register(callNode.getFunctionRegister, call))
        st_with_binding -> st_with_binding.getOrCreateSymbolicVar(Register(callNode.getFunctionRegister, call))
      }
      else {
        val st_with_base_binding = st.withLocalBinding(Register(callNode.getBaseRegister, call))
        val baseSV = st_with_base_binding.getOrCreateSymbolicVar(Register(callNode.getBaseRegister, call))
        if(callNode.getPropertyString != null)
          st_with_base_binding.addConstraint(HeapConstraint(Right(baseSV),Left(callNode.getPropertyString), st_with_base_binding.getFreshVar )) -> st_with_base_binding.getFreshVar
        else {
          val st_with_prop_binding = st_with_base_binding.withLocalBinding(Register(callNode.getPropertyRegister,call))
          val propSV = st_with_prop_binding.getOrCreateSymbolicVar(Register(callNode.getPropertyRegister, call))
          st_with_prop_binding.addConstraint(HeapConstraint(Right(baseSV),Right(propSV), st_with_prop_binding.getFreshVar)) -> st_with_prop_binding.getFreshVar
        }
      }
    }

    forwards.getCalleeExits(call).getFirst flatMap { callee =>

      // Binds the return value of the function to the result of the call, and the `this` variable within the function to the receiver of the call
      def bindThisAndRes : AbstrStore => AbstrStore = { store =>
        val this_bound = (store /: store.localConstraints) { case (acc, LocalConstraint(src, snk, closure)) =>
          if (src == Register(call.getNode.asInstanceOf[CallNode].getBaseRegister,call))
            acc addConstraint LocalConstraint(Variable("this", callee), snk, closure)
          else
            acc
        }
        store.getSymbolicVar(resReg) match {
          case Some(resSymVar) if store constrains resSymVar =>
            this_bound addConstraint LocalConstraint(Register(callee.getNode.asInstanceOf[ReturnNode].getReturnValueRegister, callee), resSymVar, None)
          case _ => this_bound
        }
      }

      // Process closure local constraints either scoped to this callee, or belonging to a closure of this callee.
      // A simple JS Example, for reference in comments below: `function f(x){var n = x ; return function g(){return n;}}`
      //   in which each call to f (the scope of n) generates a different closure on g
      stores.flatMap { st =>
        val closureInstances = st.localConstraints.flatMap{_.closure}.filter{_._2 == callee.getNode.getBlock.getFunction}.toSet
        def localMatchesFn(frame : (SymbolicVar,Function))(lc: LocalConstraint): Boolean = lc.closure exists frame.equals
        val (st_with_binding, fnInstanceSV) = bindFnInstance(st)
        //First, for each local constraint belonging to a closure on the callee, either this call is the same closure, or a different one - generate one query for each case.
        // E.G. closure local constraint on n at a call to g in the example above
        val closureLocalsProcessed = (((st_with_binding->Nil)::Nil:Iterable[(AbstrStore,Iterable[Constraint])]) /: closureInstances){case (accStores, currFn) =>
          accStores flatMap {case (s, stack_frame) =>
            val closureLocals = s.localConstraints.filter(localMatchesFn(currFn))
            val inSameClosure = s.addConstraint(ClosureConstraint(currFn._1, fnInstanceSV, true)) -> stack_frame
            val inDiffClosure = s.addConstraint(ClosureConstraint(currFn._1, fnInstanceSV, false)).dropConstraints(closureLocals.contains) -> (stack_frame ++ closureLocals)
            inSameClosure :: inDiffClosure :: Nil
          }
        }

        //Then, for each closure local constraint where the variable is scoped to this callee, this execution of the callee either does or does not correspond to that closure.
        // E.G. closure local constraints on n at a call to f in the example above.
        val scopeLocals= st.localConstraints.filter {case LocalConstraint(v@Variable(_,scope),snk,Some((clInstance, fn))) => scope == callee.getNode.getBlock.getFunction ; case _ => false}
        (closureLocalsProcessed /: scopeLocals) {case (acc,curr) =>
            acc.flatMap{ case (s,frame) =>
              (s.addConstraint(ScopeConstraint(curr.closure.get._1, curr.closure.get._2, curr.src.asInstanceOf[Variable].scope, true)) -> frame) ::
                s.dropConstraint(curr).addConstraint(ScopeConstraint(curr.closure.get._1, curr.closure.get._2, curr.src.asInstanceOf[Variable].scope, false)) -> (frame ++ Some(curr)):: Nil
            }
        }
      }.groupBy{_._2/*same stack frame to push*/}.map { case (frame, stores) => //Finally, group store/stack-frame pairs by stack-frame, and generate a disjunct-state for each stack frame equivalence class
        DisjunctState(callee, stores.map(st => bindThisAndRes(st._1)).toSet, stack push (call -> frame), loopCtx)
      }
    }
  }

  /** jump from a constructor CallNode to its callees, scoping out locals, binding `this` within each callee to the result of the call */
  def doConstructorExit(call: ProgramLocation, stores: Iterable[AbstrStore], stack: Stack[(ProgramLocation,Iterable[Constraint])], loopCtx : Stack[(ProgramLocation,AbstrStore)]): Iterable[DisjunctState] = {
    val res = Register(call.getNode.asInstanceOf[CallNode].getResultRegister, call)
    val fn = Register(call.getNode.asInstanceOf[CallNode].getFunctionRegister, call)
    forwards.getCalleeExits(call).getFirst map { callee =>
      DisjunctState(callee, stores.map{ store =>
        //First we bind the prototype of the constructed object to the `prototype` field of the function, yielding store'
        val relevant_protos = store.protoConstraints.filter { pc => store.getSymbolicVar(res) == Some(pc.child) }
        val protos_processed: AbstrStore = (store /: relevant_protos) { (store, proto) =>
          val temp = store.withLocalBinding(fn)
          val fn_sym_var = temp.getSymbolicVar(fn).get
          val (temp2, fn_proto) = temp.heapConstraints.find { hc => hc.rcvr == Right(fn_sym_var) && hc.prop == Left("prototype") } match {
            case None =>
              val freshVar = temp.getFreshVar
              (temp.addConstraint(HeapConstraint(Right(fn_sym_var), Left("prototype"), freshVar)), freshVar)
            case Some(hc) => (temp, hc.snk)
          }
          temp2 dropConstraint proto addConstraint proto.addProtoRelationship(proto.child, fn_proto)
        }
        protos_processed.getSymbolicVar(res) match {
          case Some(resSymVar) if store constrains resSymVar =>
            protos_processed addConstraint LocalConstraint(Variable("this", callee), resSymVar, None)
          case _ => protos_processed
        }
      }.toSet, stack push (call -> Nil), loopCtx)

    }
  }

  /**
    * Jump from a function entrypoint to either
    * - the call on top of the stack OR
    * - all callers of the function, if the stack is empty.
    * scoping caller local variables back in,
    * marking as undefined all callee locals that were never assigned,
    * and binding formals to actuals.
    *
    * @return
    */
  def doCallEntry(fnEntry: ProgramLocation, stores: Iterable[AbstrStore], stack: Stack[(ProgramLocation,Iterable[Constraint])], loopCtx : Stack[(ProgramLocation,AbstrStore)]): Set[DisjunctState] = {
    val jumpTargets: Iterable[(ProgramLocation,Iterable[Constraint])] =
      stack.headOption.fold[Iterable[(ProgramLocation,Iterable[Constraint])]] (forwards.getCallSites(fnEntry) map {_ -> Nil})(_ :: Nil)
    jumpTargets map { case (caller,stashed_constraints) =>
      val res_stores: Set[AbstrStore] = caller.getNode match {
        case c: CallNode =>
          // When the call node uses Function.prototype.call, argument indices are shifted up by one to accomodate `thisArg` as the first argument.
          val argumentShift = if (c.getPropertyString == "call" && forwards.getCalleeExits(caller).getSecond.contains(ECMAScriptObjects.FUNCTION_CALL)) 1 else 0

          stores.flatMap { store =>
            //Bind "this" variable to receiver of call
            val st_this_bound = store.getSymbolicVar(Variable("this", fnEntry)) match {
              case None => store
              case Some(thisSV) =>
                if (c.isConstructorCall)
                  store
                else {
                  val store_with_binding = store.withLocalBinding(Register(c.getBaseRegister, caller))
                  store_with_binding.substitute(thisSV, store_with_binding.getSymbolicVar(Register(c.getBaseRegister, caller)).get)
                }
            }
            //Process heap constraints on this function's "arguments" array
            val argsArray = forwards.get(fnEntry, new forwards_backwards_api.memory.Variable("arguments"))
            val argsConstraints = store.heapConstraints.filter { hc =>
              hc.prop.isLeft &&
                hc.rcvr.fold({ v => v.isMaybe(argsArray) }, { _ => false })
            }
            ((Some(st_this_bound): Option[AbstrStore]) /: argsConstraints) { case (opt_st, hc) => opt_st flatMap { st =>
              if (hc.prop.left.get == "length")
                BackwardsTransfer.writePure(st dropConstraint hc, fnEntry, hc.snk, Value makeNum c.getNumberOfArgs, forwards)
              else
                Try(hc.prop.left.get.toInt) match {
                  case Success(formalIdx) if formalIdx < c.getNumberOfArgs =>
                    val paramRegister = Register(c.getArgRegister(formalIdx + argumentShift), caller)
                    Some(st dropConstraint hc addConstraint LocalConstraint(paramRegister, hc.snk, None))
                  case Success(_) /* fall through implies formalIdx > c.getNumberOfArgs, so this argument is undefined*/ =>
                    BackwardsTransfer.writePure(st dropConstraint hc, fnEntry, hc.snk, Value makeUndef, forwards)
                  case Failure(_) => Some(st)
                }
            }
            }
          }.flatMap{st => //Refute stores with violated (positive) scope constraints and drop satisfied (negative) scope constraints
            val relevantScopeConstraints = st.scopeConstraints.filter{_.scope_fn == fnEntry.getNode.getBlock.getFunction}
            if(relevantScopeConstraints exists {_.asserting}) None else Some(st dropConstraints relevantScopeConstraints.contains)
          }.map { store => //Then, bind formals to actuals and re-add any stashed constraints from the original call
            val formalsToActualsMap: Iterable[(String, Int)] = fnEntry.getNode.getBlock.getFunction.getParameterNames.zip((argumentShift until c.getNumberOfArgs).map(c.getArgRegister).padTo(fnEntry.getNode.getBlock.getFunction.getParameterNames.size, -1))
            (store.addConstraints(stashed_constraints) /: formalsToActualsMap) { case (st, (formal, actual)) =>
              st.getLocalBinding(Variable(formal, fnEntry)) match {
                case Some(local) =>
                  if (actual == -1) {
                    //Fewer actual arguments than formal parameters, so this formal is undefined
                    st.dropConstraint(local).addConstraint(PureConstraint.make_eq(local.snk, Value makeUndef, fnEntry))
                  } else st.dropConstraint(local).addConstraint(LocalConstraint(Register(actual, caller), local.snk, None))
                case None => st
              }
            }
          }.map{ store => //Finally, for each local constraint whose scope is a closure on this function, tag that constraint with a corresponding closure symbolic var
            def scopeChain : Function => List[Function] = {f => f.getOuterFunction match {case null => f::Nil ; case fOuter => f::scopeChain(fOuter)}}
            val closureLocals = store.localConstraints.filter {
              case LocalConstraint(v:Variable, snk, None) => (!v.scope.isMain) && (v.scope != fnEntry.getNode.getBlock.getFunction) && scopeChain(fnEntry.getNode.getBlock.getFunction).contains(v.scope)
              case _ => false
            }

            val (st_with_binding, fnSV) = {
              if(c.getFunctionRegister >= 0) {
                val st_with_binding = store.withLocalBinding(Register(c.getFunctionRegister, caller))
                st_with_binding -> st_with_binding.getOrCreateSymbolicVar(Register(c.getFunctionRegister, caller))
              }
              else {
                val st_with_base_binding = store.withLocalBinding(Register(c.getBaseRegister, caller))
                val baseSV = st_with_base_binding.getOrCreateSymbolicVar(Register(c.getBaseRegister, caller))
                if(c.getPropertyString != null)
                  st_with_base_binding.addConstraint(HeapConstraint(Right(baseSV),Left(c.getPropertyString), st_with_base_binding.getFreshVar )) -> st_with_base_binding.getFreshVar
                else {
                  val st_with_prop_binding = st_with_base_binding.withLocalBinding(Register(c.getPropertyRegister,caller))
                  val propSV = st_with_prop_binding.getOrCreateSymbolicVar(Register(c.getPropertyRegister, caller))
                  st_with_prop_binding.addConstraint(HeapConstraint(Right(baseSV),Right(propSV), st_with_prop_binding.getFreshVar)) -> st_with_prop_binding.getFreshVar
                }
              }
            }

            (st_with_binding /: closureLocals) {case (st, lc) =>
                st.dropConstraint(lc)
                  .addConstraint(LocalConstraint(lc.src, lc.snk, Some(fnSV -> fnEntry)))
            }
          }.toSet
        case _ => stores.toSet
      }
      DisjunctState(
        caller,
        res_stores,
        if (stack.nonEmpty) stack.pop else stack,
        loopCtx
      )
    } toSet
  }


  /*Utility function to add a binding for the conditional variable of an IfNode to the truth value matching the branch taken*/
  private def trackConditional(condLoc : ProgramLocation, branchTaken : Boolean)(store : AbstrStore) : AbstrStore = {
    assert(condLoc.getNode.isInstanceOf[IfNode])
    val condReg = Register(condLoc.getNode.asInstanceOf[IfNode].getConditionRegister,condLoc)
    val res_store = store.withLocalBinding(condReg)
    val condSymVar = res_store getOrCreateSymbolicVar condReg
    res_store addConstraint PureConstraint(PureUnOp(UnOp.NOT,PureUnOp(UnOp.NOT, condSymVar, condLoc), condLoc), Value makeBool branchTaken, asserting = true) match {
      case sqas:SetQueryAbstrStore => SetQueryAbstrStore(sqas.constraints, sqas.trackedValue.substitute(condSymVar,Value makeBool branchTaken))
      case x:AbstrStore => x
    }
  }

  private def nodeTransferFns(stores: Iterable[AbstrStore], loc: ProgramLocation): Iterable[AbstrStore] = loc.getNode match {
    case n: BeginForInNode => stores flatMap {store => BackwardsTransfer.begin_forin(Register(n.getObjectRegister,loc),n.getIndex,store,forwards,loc)}
    case n: BeginLoopNode => stores
    case n: BeginWithNode => ???
    case n: BinaryOperatorNode => stores flatMap {store => BackwardsTransfer.binop(Register(n.getResultRegister,loc), Register(n.getArg1Register,loc), n.getOperator, Register(n.getArg2Register,loc),store,forwards,loc)}
    case n: CallNode => stores //Return value and Formal/Actual bindings are performed in BackwardsTransfer#transfer
    case n: CatchNode => ???
    case n: ConstantNode => stores flatMap {store =>
      BackwardsTransfer.const(Register(n.getResultRegister,loc),
        n.getType match {
          case Type.BOOLEAN => Value makeBool n.getBoolean
          case Type.NULL => Value makeNull
          case Type.NUMBER => Value makeNum n.getNumber
          case Type.STRING => Value makeStr n.getString
          case Type.UNDEFINED => Value makeUndef
        },
        store,forwards,loc)}
    case n: DeclareFunctionNode =>
      val result_mem : ProgramVar = if(n.isExpression || n.getFunction.getName == null) Register(n.getResultRegister,loc) else Variable(n.getFunction.getName,loc)
      stores flatMap {store => BackwardsTransfer.decl_fn(result_mem, n.getFunction, store, forwards, loc)}
    case n: DeclareVariableNode => stores flatMap {store => BackwardsTransfer.decl_var(Variable(n.getVariableName, loc), store, forwards, loc)}
    case n: DeletePropertyNode => ???
    case n: EndForInNode => stores // No op; Logic of binding properties is handles in BackwardsTransfer#transfer (BeginForInNode and EndForInNode cases)
    case n: EndLoopNode => stores
    case n: EndWithNode => ???
    case n: EventDispatcherNode => ???
    case n: ExceptionalReturnNode => ???
    case n: HasNextPropertyNode => stores // No op; Logic of binding properties is handles in BackwardsTransfer#transfer (BeginForInNode and EndForInNode cases)
    case n: IfNode =>
      // Avoid irrelevant path-sensitivity.
      //  That is, if there are any stores with opposite constraints on this loop conditions (i.e. one came from true branch, one from false branch)
      //    ... combine them into a single store with no constraint on the loop condition
      // NOTE this code is brittle to generation of loop condition constraints, in BackwardsTransfer#transfer (IfNode case)

      /** helper function to grab the constraint on the loop condition. */
      def getBranchConstraint : AbstrStore => PureConstraint = { st =>
        val condSV = st.getOrCreateSymbolicVar(Register(n.getConditionRegister,loc))
        st.pureConstraints.find {pc => pc.lhs.negationsAndBase._2 match {case PureVar(`condSV`) => true ; case _ => false}}.get
      }

      stores.groupBy(_.getSymbolicVar(Register(n.getConditionRegister,loc))).flatMap{ case (Some(condSymVar),storesWithSameVar) =>
        storesWithSameVar.partition{s =>
          val branchConstraint = s.pureConstraints.find{case PureConstraint(PureUnOp(UnOp.NOT,PureUnOp(UnOp.NOT, PureVar(`condSymVar`), _),_), _, true) => true ; case _ => false}
          if (branchConstraint.isDefined) branchConstraint.get.rhs.isMaybeTrueButNotFalse else false
        } match {
          case (l,r) if l.isEmpty => r
          case (l,r) if r.isEmpty => l
          case (l,r) =>
            val matched_pairs = l flatMap {l_st => r.find {r_st =>
              l_st.dropConstraint(getBranchConstraint(l_st)) == r_st.dropConstraint(getBranchConstraint(r_st))
            } map l_st.-> }
            val (ls_with_matches, rs_with_matches) = (matched_pairs map {_._1}, matched_pairs map {_._2})
            (l.toSet -- ls_with_matches) ++ (r.toSet -- rs_with_matches) ++ (rs_with_matches map {st => st.dropConstraint(getBranchConstraint(st))})
        }
        case _ => sys.error(s"Unreachable case, since loop condition should always be generated in BackwardsTransfer#transfer");
      }
    case n: NewObjectNode => stores flatMap {store => BackwardsTransfer.new_obj(Register(n.getResultRegister,loc),n,store, forwards, loc)}
    case n: NextPropertyNode => stores flatMap {store => BackwardsTransfer.next_prop(Register(n.getPropertyRegister,loc),store,forwards,loc)}
    case n: NopNode => stores
    case n: ReadPropertyNode => stores flatMap {store => BackwardsTransfer.read_prop(Register(n.getResultRegister,loc),Register(n.getBaseRegister,loc), Register(n.getPropertyRegister,loc), n.getPropertyString, store,forwards,loc)}
    case n: ReadVariableNode => stores flatMap {store => BackwardsTransfer.read_var(Variable(n.getVariableName, getScopeFn(n.getVariableName, loc)), Register(n.getResultRegister,loc), store, forwards, loc)}
    case n: ReturnNode => stores //binding of return variables to correct symbolic variable is handled at call site, so this is a no-op
    case n: ThrowNode => None
    case n: TypeofNode => stores flatMap {store => BackwardsTransfer.typeof(Register(n.getResultRegister,loc), if(n.isVariable) Variable(n.getVariableName, getScopeFn(n.getVariableName, loc)) else Register(n.getArgRegister,loc), store, forwards, loc)}
    case n: UnaryOperatorNode => stores flatMap {store => BackwardsTransfer.unop(Register(n.getResultRegister,loc), n.getOperator, Register(n.getArgRegister,loc), store, forwards, loc)}
    case n: WritePropertyNode => stores flatMap {store => BackwardsTransfer.write_prop(Register(n.getValueRegister,loc), Register(n.getBaseRegister,loc), Register(n.getPropertyRegister,loc), n.getPropertyString, store, forwards, loc)}
    case n: WriteVariableNode => stores flatMap {store => BackwardsTransfer.write_var(Variable(n.getVariableName, getScopeFn(n.getVariableName, loc)), Register(n.getValueRegister,loc), store)}
  }
}


object BackwardsTransfer {
  def begin_forin(loopObjReg: Register, loopID: Int, store: AbstrStore, f: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = {
    val new_store = store.withLocalBinding(loopObjReg)
    val loopObjSymVar = new_store.getSymbolicVar(loopObjReg).get
    store.loopConstraints.find { _.loopHead.getIndex == loopID }.map { lc =>
      (new_store.dropConstraint(lc) /: lc.propValues) { (st, prop) => st.addConstraint(ProtoConstraint(loopObjSymVar, Some(loopObjSymVar), Left(prop))) }
    }

  }

  def binop(resultReg: Register, lhsReg: Register, op: BinaryOperatorNode.Op, rhsReg: Register, store: AbstrStore, forwards: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = {
    store.getLocalBinding(resultReg) match {
      case Some(local@LocalConstraint(_, resSymVar, _)) if store constrains resSymVar =>
        val new_store = store.withLocalBinding(lhsReg).withLocalBinding(rhsReg).dropConstraint(local)
        val (lhsSymVar, rhsSymVar) = (new_store.getSymbolicVar(lhsReg).get, new_store.getSymbolicVar(rhsReg).get)
        val rhs: PureExpr = if (op == BinaryOperatorNode.Op.IN) forwards.get(loc, new forwards_backwards_api.memory.Register(rhsReg.num)) else rhsSymVar
        writePure(new_store, loc, resSymVar, PureBinOp(lhsSymVar, op, rhs, loc), forwards)
      case _ => Some(store) //register being written to is unconstrained; leave store unchanged
    }
  }

  def const(resultReg: Register, constant: Value, store: AbstrStore, forwards: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = store.getLocalBinding(resultReg) match {
    case Some(local@LocalConstraint(_, resSymVar, _)) if store constrains resSymVar =>
      writePure(store dropConstraint local, loc, resSymVar, constant, forwards)
    case _ => Some(store) // register being written to is unconstrained; leave store unchanged
  }

  def decl_fn(resultMem: ProgramVar, fn: dk.brics.tajs.flowgraph.Function, store: AbstrStore, forwards: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = {
    store.getLocalBinding(resultMem) match {
    case Some(local@LocalConstraint(_, resSymVar, _)) =>
      // First, process any closure/scope constraints on the function being declared here
      val closureConstraintsProcessed = ((Some(store):Option[AbstrStore]) /: store.constraints) {
        case (acc,c@ClosureConstraint(cl1, cl2, false)) if cl1 == resSymVar ^ cl2 == resSymVar => acc map {_ dropConstraint c}
        case (acc,c@ClosureConstraint(cl1, cl2,  true)) if cl1 == resSymVar ^ cl2 == resSymVar => None
        case (acc,s@ScopeConstraint(`resSymVar`, `fn`, _, true)) => acc map {_ dropConstraint s}
        case (acc,s@ScopeConstraint(`resSymVar`, `fn`, _, false)) => None
        case (acc,_) => acc
      }
      // Then, write the abstract function corresponding to this declaration to any pure constraints
      val abstrFnWritten = closureConstraintsProcessed flatMap {st => writePure(st dropConstraint local, loc, resSymVar, forwards.get(loc, resultMem), forwards)}

      // Then, bind the result to the TAJS abstract object and assign the "prototype" field of the declared function
      (abstrFnWritten /: store.protoConstraints) { (optStore, pc) =>
        if (pc.child == resSymVar) {
          if ((pc.upperBounds contains resSymVar) || pc.parent.isEmpty) None
          else optStore map { s => s.dropConstraint(pc).substitute(resSymVar, pc.parent.get) }
        }
        else optStore
      } map { s =>
        val constraints = s.map {
          // Finally, resolve any heap constraints on the function to be undefined, as in NewObjectNode
          case HeapConstraint(`resSymVar`, _, snk) => PureConstraint(snk, Value.makeUndef, asserting = true)
          case x => x
        } toSet

        s match {
          case s: SetQueryAbstrStore => SetQueryAbstrStore(constraints, s.trackedValue)
          case _ => constraints2store(constraints)
        }

      }
    case None => Some(store)
  }}

  def decl_var(variable: Variable, store: AbstrStore, forwards: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = { Some(store) }

  // Constrain the resulting object to be from this allocation site, AND
  // all heap constraints whose receiver is this new object are now known to point to `undefined`
  def new_obj(resultReg: Register, srcNode: AbstractNode, store: AbstrStore, forwards: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = {
    val baseObj = forwards.get(loc, new forwards_backwards_api.memory.Register(resultReg.num))
    store.getLocalBinding(resultReg) match {
      case Some(local@LocalConstraint(_, resSymVar, _)) =>
        //Resolve proto constraints from this object to Object.prototype (i.e. inherited native functions like toString, etc.  full list in Natives.scala#getPropNames)
        val varsWithBaseObj = (store.pureConstraints flatMap store.getDefiniteValBinding).filter {
          _._2 == baseObj
        }.map {
          _._1
        }
        val protosOnObjProto = store.protoConstraints.filter { pc =>
          varsWithBaseObj.contains(pc.child) &&
            pc.prop.isLeft &&
            Natives.getPropNames(ECMAScriptObjects.OBJECT_PROTOTYPE).contains(pc.prop.left.get)
        }
        ((Some(store): Iterable[AbstrStore]) /: protosOnObjProto) { case (acc_st, curr_pc) => acc_st flatMap { st =>
          curr_pc.parent match {
            case Some(prototypeSV) =>
              val matchingHeaps = st.heapConstraints.filter { hc => hc.rcvr == Right(prototypeSV) && hc.prop == curr_pc.prop }
              ((Some(st dropConstraint curr_pc): Iterable[AbstrStore]) /: matchingHeaps) { case (ss, hc) => ss.flatMap { s =>
                val obj_prototype = ObjectLabel.make(ECMAScriptObjects.OBJECT_PROTOTYPE, Kind.OBJECT)
                val native_prop = new Property(obj_prototype, Value makeStr hc.prop.left.get)
                val native_fn = forwards.get(loc, native_prop)
                writePure(s dropConstraint hc, loc, hc.snk, native_fn, forwards)
              }
              }
            case None => None
          }
        }
        } map { st => // drop local constraint on result reg of this new object node, assert that the snk of that constraint is in fact this object.
          st dropConstraint local addConstraint PureConstraint.make_eq(resSymVar, baseObj, loc)
        }
      case _ =>
        if (store.heapConstraints.exists { hc => hc.rcvr == Left(baseObj) }) None else Some(store)
    }
  }

  def next_prop(propReg: Register, store: AbstrStore, forwards: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = {
    // For all for-in loops, pred^3(next_prop_loc)==begin_loc
    val beginLoc = forwards.getPredecessors(forwards.getPredecessors(forwards.getPredecessors(loc).head).head).head
    assert(beginLoc.getNode.isInstanceOf[BeginForInNode])
    //    val stores = BackwardsTransfer.makeStoresWithLoopCtx(beginLoc,forwards,store::Nil)
    val storesAndContexts: Iterable[(AbstrStore, ForInLoopCtxConstraint)] =
      store.loopConstraints.find {
        _.loopHead == beginLoc.getNode
      } match {
        case Some(forinLoopCtx) => Some((store, forinLoopCtx))
        case None =>
          BackwardsTransfer.makeStoresWithLoopCtx(beginLoc, forwards, store :: Nil) map { st => st -> st.loopConstraints.find {
            _.loopHead == beginLoc.getNode
          }.get
          }
      }
    storesAndContexts flatMap { case (st, ctx) =>
      st.getLocalBinding(propReg) match {
        case Some(resBinding) if st constrains resBinding.snk => writePure(st dropConstraint resBinding, loc, resBinding.snk, Value makeStr ctx.propValue, forwards)
        case _ => Some(st)
      }
    }
  }

  def read_prop(resultReg: Register, baseReg: Register, propReg: Register, propString: String, store: AbstrStore, f: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = {
    val localResBinding = store.getLocalBinding(resultReg)
    if (localResBinding.isEmpty || !store.constrains(localResBinding.get.snk)) return Some(store)

    def read_prop_explicit(baseObj: Value, prop: Either[String, SymbolicVar], store: AbstrStore): Iterable[AbstrStore] = {
      val protosWithSameBase: Iterable[ProtoConstraint] = store.protoConstraints.filter { x => Some(x.child) == store.getSymbolicVar(baseReg) }
      val protosIntersectedWithForwards = ((Some(store): Iterable[AbstrStore]) /: protosWithSameBase) { (opt_st, pc) => opt_st flatMap { st =>
        val matchingHeaps = st.heapConstraints.filter { hc => hc.rcvr.right.toOption == pc.parent && pc.parent.isDefined && hc.prop == pc.prop && hc.prop.isLeft }
        ((Some(st dropConstraint pc): Option[AbstrStore]) /: matchingHeaps) { (opt_st, hc) => opt_st flatMap { st =>
          writePure(st dropConstraint hc, loc, hc.snk, f.get(loc, new Property(baseObj.getObjectLabels.head, Value makeStr pc.prop.left.get)), f)
        }
        }
      }
      }
      val allHeapConstraints: Iterable[HeapConstraint] = protosIntersectedWithForwards flatMap {
        _.heapConstraints
      }
      val heapsIntersectedWithForwards = (protosIntersectedWithForwards /: allHeapConstraints) { (opt_st, hc) =>
        hc.rcvr match {
          case Left(rcvr) if (rcvr isMaybe baseObj) && (Some(propString) == hc.prop.left.toOption) => opt_st flatMap { st =>
            writePure(st dropConstraint hc, loc, hc.snk, f.get(loc, new Property(baseObj.getObjectLabels.head, Value makeStr propString)), f).flatMap {
              case st_with_forwards_intersect if st_with_forwards_intersect.isSatisfiable(f, loc) =>
                if (baseObj.getObjectLabels.head.isHostObject) Some(st_with_forwards_intersect)
                else Some(st)
              case _ => None
            }
          }
          case _ => opt_st
        }
      }

      heapsIntersectedWithForwards flatMap { s =>
        s.getLocalBinding(resultReg) match {
          case Some(local) if baseObj.getObjectLabels.head.isHostObject && propString != null =>
            writePure(s dropConstraint local, loc, local.snk, f.get(loc, new Property(baseObj.getObjectLabels.head, Value makeStr propString)), f)
          case Some(local) =>
            Some(s dropConstraint local addConstraint HeapConstraint(Left(baseObj), prop, local.snk))
          case None => Some(s)
        }
      }
    }

    if (propString != null) {
      val baseVal = f.get(loc, baseReg)
      val protoObjects = baseVal.getObjectLabels flatMap { obj => f.getPrototypeObjects(loc, obj, Value makeStr propString) }
      protoObjects.size match {
        case 0 =>
          return BackwardsTransfer.const(resultReg, Value makeUndef, store, f, loc)
        case 1 if baseVal.getObjectLabels.head.isSingleton =>
          return read_prop_explicit(Value makeObject protoObjects.head, Left(propString), store)
        case _ => //NO-OP - fall through to prototype logic below.
      }
    } else {
      val baseVal = f.get(loc, baseReg)
      val propValue = f.get(loc, propReg)
      val protoObjects = baseVal.getObjectLabels flatMap { obj => f.getPrototypeObjects(loc, obj, propValue) }
      protoObjects.size match {
        case 0 => return BackwardsTransfer.const(resultReg, Value makeUndef, store, f, loc)
        case 1 =>
          val swb = store.withLocalBinding(propReg)
          val propSV = swb.getSymbolicVar(propReg).get
          return read_prop_explicit(Value makeObject protoObjects.head, Right(propSV), swb)
        case _ => // NO-OP - fall through to prototype logic below.
      }
    }

    assert(propReg != null || propString != null)
    if (propString == "__proto__") {
      //Prototype chain read special case
      val store_with_bindings = store.withLocalBinding(resultReg).withLocalBinding(baseReg)
      val (baseSV, resSV) = (store_with_bindings.getSymbolicVar(baseReg).get, store_with_bindings.getSymbolicVar(resultReg).get)
      Some(store_with_bindings map { case pc: ProtoConstraint => pc.addProtoRelationship(baseSV, resSV); case x => x }): Option[AbstrStore]
    } else if (propString == "length") {
      Some(store.getLocalBinding(resultReg) match {
        case Some(local) if store constrains local.snk =>
          store dropConstraint local addConstraint HeapConstraint(Right(store.getOrCreateSymbolicVar(baseReg)), Left("length"), local.snk)
        case _ => store
      })
    } else {
      store.getLocalBinding(resultReg) match {
        case Some(local@LocalConstraint(_, resSV,_)) if store constrains resSV =>
          val (store_with_bindings, prop) = propString match {
            //Is this read dynamic or static?
            case null => //Dynamic read
              val swb = store.dropConstraint(local).withLocalBinding(baseReg).withLocalBinding(propReg)
              val propSV = swb.getSymbolicVar(propReg).get
              (swb, Right(propSV))
            case propStr => //Static read
              val swb = store.dropConstraint(local).withLocalBinding(baseReg)
              (swb, Left(propStr))
          }
          val freshSV = store_with_bindings.getFreshVar
          val undefResult = writePure(store_with_bindings.addConstraint(ProtoConstraint(store_with_bindings.getSymbolicVar(baseReg).get, None, prop)), loc, resSV, Value.makeUndef, f).map { st =>
            st.addConstraint(PureConstraint.make_eq(resSV, Value.makeUndef, loc))
              .addConstraint(HeapConstraint(Right(store_with_bindings.getOrCreateSymbolicVar(baseReg)), prop, resSV))
          }
          Seq(store_with_bindings.addConstraint(ProtoConstraint(store_with_bindings.getSymbolicVar(baseReg).get, Some(freshSV), prop)).addConstraint(HeapConstraint(Right(freshSV), prop, resSV))) ++ undefResult
        case _ => Some(store)
      }
    }
  }
  def read_var(variable : Variable, resultReg : Register, store : AbstrStore, f : Forwards, loc : ProgramLocation) : Iterable[AbstrStore] = store.getLocalBinding(resultReg) match {
      case None => Some(store)
      case Some(resLocal) if variable.name == "undefined" => writePure(store dropConstraint resLocal, loc, resLocal.snk, Value makeUndef, f)
      case Some(resLocal) if variable.name == "js_value_refiner_debug_top" => writePure(store dropConstraint resLocal, loc, resLocal.snk, AbstractValue.top_non_obj, f)
      case Some(resLocal) =>
        val tajs_query_val = f.get(loc, variable)

        // Handle "variables" that are actually native objects (e.g. "Array", "Object", etc.
        if (tajs_query_val.isMaybeSingleObjectLabel &&
          tajs_query_val.getObjectLabels.head.getHostObject != null &&
          tajs_query_val.getObjectLabels.head.getHostObject.toString == variable.name) {
          // if(forwards.get(location,variable) is a singleton object whose sole objectlabel's hostobject.toString = variable.name, write that native object
          //And, for any heap constraints on the object, write the appropriate native function if possible
          val relevantProtos = store.protoConstraints.filter {
            _.child == resLocal.snk
          }

          ((Some(store): Option[AbstrStore]) /: relevantProtos) { (opt_st, pc) =>
            opt_st flatMap { st =>
              val heapConstraints = st.heapConstraints.filter { hc => hc.rcvr.right.toOption == pc.parent && pc.parent.isDefined && hc.prop.isLeft && hc.prop == pc.prop }
              ((Some(st dropConstraint pc): Option[AbstrStore]) /: heapConstraints) { (opt_st, hc) =>
                val native_prop_val = f.get(loc, new forwards_backwards_api.memory.Property(tajs_query_val.getObjectLabels.head, Value makeStr pc.prop.left.get))
                opt_st flatMap { s => writePure(s.dropConstraint(hc), loc, hc.snk, native_prop_val, f) }
              }
            }
          } flatMap { store => writePure(store dropConstraint resLocal, loc, resLocal.snk, tajs_query_val, f) }
        }
        else
          Some(store dropConstraint resLocal addConstraint LocalConstraint(variable, resLocal.snk, None))
    }

  def typeof(resultReg : Register, argument : ProgramVar, store : AbstrStore, forwards : Forwards, loc : ProgramLocation) : Iterable[AbstrStore] = {
    val store_with_arg_binding = store.withLocalBinding(argument)
    val argSV = store_with_arg_binding.getSymbolicVar(argument).get
    store_with_arg_binding.getLocalBinding(resultReg) match {
      case Some(local@LocalConstraint(_, resSV, _)) if store_with_arg_binding constrains resSV =>
        val forwardsArgBound = forwards.get(loc,argument)
        val (isMaybeUndef, isMaybeNull, isMaybeBool, isMaybeNum, isMaybeStr, isMaybeObj, isMaybeFun) = (
          forwardsArgBound.isMaybeUndef,
          forwardsArgBound.isMaybeNull,
          forwardsArgBound.isMaybe(Value makeAnyBool),
          forwardsArgBound.isMaybe(Value makeAnyNum),
          forwardsArgBound.isMaybe(Value makeAnyStr),
          forwardsArgBound.getObjectLabels.exists{_.getKind != Kind.FUNCTION},
          forwardsArgBound.getObjectLabels.exists{_.getKind == Kind.FUNCTION})

        (if(isMaybeUndef) writePure(//arg is undefined
          store_with_arg_binding.dropConstraint(local).addConstraint(PureConstraint.make_eq(argSV,Value.makeUndef,loc)),
          loc, resSV, Value makeStr "undefined", forwards) else None) ++
          (if(isMaybeNull) writePure(//arg is null
            store_with_arg_binding.dropConstraint(local).addConstraint(PureConstraint.make_eq(argSV,Value.makeNull,loc)),
            loc, resSV, Value makeStr "object", forwards) else None) ++
          (if(isMaybeBool) writePure(//arg is a boolean
            store_with_arg_binding.dropConstraint(local).addConstraint(PureConstraint.make_eq(argSV,Value.makeAnyBool,loc)),
            loc, resSV, Value makeStr "boolean", forwards) else None) ++
          (if(isMaybeNum) writePure(//arg is a number
            store_with_arg_binding.dropConstraint(local).addConstraint(PureConstraint.make_eq(argSV,Value.makeAnyNum,loc)),
            loc, resSV, Value makeStr "number", forwards) else None) ++
          (if(isMaybeStr) writePure(//arg is a string
            store_with_arg_binding.dropConstraint(local).addConstraint(PureConstraint.make_eq(argSV,Value.makeAnyStr,loc)),
            loc, resSV, Value makeStr "string", forwards) else None) ++
          (if(isMaybeObj) writePure(//arg is an object.  TAJS has no "top" for the object lattice, so we just say it's an object if it's not undefined,bool,num,or str
            store_with_arg_binding.dropConstraint(local).addConstraint(PureConstraint.make_diseq(argSV,Seq(Value.makeUndef, Value.makeAnyBool, Value.makeAnyNum, Value.makeAnyStr) reduceLeft {_ join _},loc)),
            loc, resSV, Value makeStr "object", forwards) else None) ++
          (if(isMaybeFun) writePure(//arg is an object.  TAJS has no "top" for the object lattice, so we just say it's an object if it's not undefined,bool,num,or str
            store_with_arg_binding.dropConstraint(local).addConstraint(PureConstraint.make_diseq(argSV,Seq(Value.makeUndef, Value.makeAnyBool, Value.makeAnyNum, Value.makeAnyStr) reduceLeft {_ join _},loc)),
            loc, resSV, Value makeStr "function", forwards) else None)
      case _ => Some(store)
    }
  }

  def unop(resultReg : Register, op : UnaryOperatorNode.Op, argReg : Register , store : AbstrStore, forwards : Forwards, loc : ProgramLocation) : Iterable[AbstrStore] = {
    store.getLocalBinding(resultReg) match {
      case Some(local@LocalConstraint(_,resSymVar,_)) if store constrains resSymVar =>
        val new_store = store.withLocalBinding(argReg)
        val exprSymVar = new_store.getSymbolicVar(argReg).get
        writePure(new_store, loc, resSymVar, PureUnOp(op,exprSymVar,loc),forwards)
      case _ => Some(store) //register being written to is unconstrained; leave store unchanged
    }
  }

  def write_prop(valueReg : Register, rcvrReg : Register, propReg : Register, propString : String, store : AbstrStore, f : Forwards, loc : ProgramLocation) : Iterable[AbstrStore] = {
    if (propString == "__proto__") {
      val store_with_bindings = store.withLocalBinding(rcvrReg).withLocalBinding(valueReg)
      val (baseSV, valSV) = (store_with_bindings.getSymbolicVar(rcvrReg).get, store_with_bindings.getSymbolicVar(valueReg).get)
      val new_constraints = store_with_bindings.constraints map { case pc: ProtoConstraint => pc.addProtoRelationship(baseSV, valSV); case x => x }
      store match {
        case sqas : SetQueryAbstrStore => Some(SetQueryAbstrStore(new_constraints,sqas.trackedValue))
        case _ => Some(AbstrStore(new_constraints))
      }
    } else {
      propString match {
        case null => //Dynamic write
          val store_with_binding = store.withLocalBinding(propReg)
          val propSV = store_with_binding.getSymbolicVar(propReg).get
          val baseVal = f.get(loc, rcvrReg)

          def bindPropToProgramVar(prop : Either[String,SymbolicVar], pv : ProgramVar, equal : Boolean)(store : AbstrStore) : AbstrStore = prop match {
            case Left(str)          => store addConstraint LocalConstraint(pv,store.getFreshVar, None) addConstraint PureConstraint(store.getFreshVar, Value makeStr str, equal)
            case Right(sv) if equal => store addConstraint LocalConstraint(pv, sv, None)
            case Right(sv)          => store addConstraint LocalConstraint(pv,store.getFreshVar, None) addConstraint PureConstraint.make_diseq(store.getFreshVar,sv,loc)
          }

          val store_explicitHeapConstraintsProcessed : Iterable[AbstrStore] = ((store_with_binding::Nil) /: store.heapConstraints) {
            case (stores, hc@HeapConstraint(Left(v), prop, snk)) if baseVal isMaybe v => stores flatMap {st => Seq(
              bindPropToProgramVar(prop, propReg, true )(st) dropConstraint hc addConstraint LocalConstraint(valueReg, snk, None),
              bindPropToProgramVar(prop, propReg, false)(st)
            )}
            case (stores, _) => stores
          }

          //For each property, either this write's property does (case S2) or doesn't (case S1) match
          //In the case that it does,
          // For each prototype constraint with that property, either this write does or does not flow to the read that generated that constraint
          (store_explicitHeapConstraintsProcessed.map {_.dropConstraints(_.isInstanceOf[ProtoConstraint])} /: store_with_binding.protoConstraints.groupBy {_.prop}) { case (acc_stores, (prop, protos)) =>

            val S1 = acc_stores map { st => st addConstraints protos addConstraint PureConstraint.make_diseq(prop.fold({ s => PureVal(Value makeStr s) }, PureVar.apply), propSV, loc) }
            val S2 =
              (acc_stores.map {
                _.addConstraint(prop.fold({ str => PureConstraint(propSV, Value makeStr str, asserting = true) }, { sv => PureConstraint.make_eq(propSV, sv, loc) }))
              }
                /: protos) { (stores, proto) =>

                val flows = if (proto.parent.isEmpty) Nil
                else stores map { st =>
                  val res_with_valueReg_bound =
                    st.addConstraint(proto.addVarWithProp(proto.parent.get))
                      .addConstraint(LocalConstraint(rcvrReg, proto.parent.get, None))
                      .withLocalBinding(valueReg)
                  res_with_valueReg_bound addConstraint HeapConstraint(Right(proto.parent.get), prop, res_with_valueReg_bound.getSymbolicVar(valueReg).get)
                }
                val doesnt_flow = stores map {
                  _.withLocalBinding(rcvrReg).addConstraint(proto addUpperBound store.getOrCreateSymbolicVar(rcvrReg))
                }
                flows ++ doesnt_flow
              }
            S1 ++ S2
          }.flatMap{st =>
            // Then, for each heap constraint that could be pointing at the same field being written to at this node,
            //  generate two disjuncts: either the fields match (sameField) or they don't (diffProp, diffRcvr)
            val closureHeapConstraints = {
              val closureSVs = st.scopeConstraints.map{_.sv} ++ st.localConstraints.flatMap{_.closure.map{_._1}}
              st.heapConstraints.filter { hc => closureSVs contains hc.snk }
            }
            ((st::Nil:Iterable[AbstrStore]) /: closureHeapConstraints){case (acc_stores, curr_hc) => acc_stores flatMap {st =>
              val st_with_bindings = st.withLocalBinding(rcvrReg).withLocalBinding(propReg)
              val rcvrSV = st_with_bindings getOrCreateSymbolicVar rcvrReg
              val propSV = st_with_bindings getOrCreateSymbolicVar propReg
              val sameField = st_with_bindings.dropConstraint(curr_hc)
                                              .addConstraint(LocalConstraint(valueReg, curr_hc.snk, None))
                                              .addConstraint(PureConstraint.make_eq(curr_hc.rcvr.fold[PureExpr]({x=>x},{x=>x}),rcvrSV,loc))
                .addConstraint(PureConstraint.make_eq(curr_hc.prop.fold[PureExpr](Value.makeStr,PureVar),propSV,loc))
              val diffRcvr = st_with_bindings.addConstraint(PureConstraint.make_diseq(curr_hc.rcvr.fold[PureExpr]({x=>x},{x=>x}),rcvrSV,loc))
              val diffProp = st_with_bindings.addConstraint(PureConstraint.make_diseq(curr_hc.prop.fold[PureExpr](Value.makeStr,PureVar),propSV,loc))
              val diffField = st_with_bindings.addConstraint(PureConstraint(
                PureBinOp(
                  PureBinOp(curr_hc.rcvr.fold[PureExpr]({x=>x},{x=>x}), BinaryOperatorNode.Op.EQ, rcvrSV, loc),
                  BinaryOperatorNode.Op.AND,
                  PureBinOp(curr_hc.prop.fold[PureExpr](Value.makeStr, PureVar), BinaryOperatorNode.Op.EQ, propSV, loc),
                  loc),
                Value makeBool true, false))
              sameField::diffField::Nil
            }}
          }

        case strLiteral => //Static write
          //For each property, either this write's property does (case S2) or doesn't (case S1) match
          // In the case that it does,
          // For each prototype constraint with that property, either this write does or does not flow to the read that generated that constraint
          val store_with_binding = store withLocalBinding rcvrReg
          val baseVal = f.get(loc, rcvrReg)
          val stores_explicitHeapConstraintsProcessed : Iterable[AbstrStore]= ((store_with_binding::Nil) /: store.heapConstraints) {
            case (stores,hc@HeapConstraint(Left(v),prop,snk))
              // UNSOUND ASSUMPTION: static writes don't flow to dynamic reads. (with the exception of explicit array constructor a la `a = [x, y, z]`
              if (baseVal isMaybe v) && prop.fold({_ == strLiteral}, {_ => Try(propString.toInt).isSuccess}) =>
              stores.flatMap {st => //For each heap constraint on an abstract object that might be the same as this write's receiver with a matching property
                //FIRST CASE: Assert properties match, process write to heap constraint
                st.dropConstraint(hc) //Drop that heap constraint
                  .addConstraints(prop.fold({_ => Nil}, {sv => Some(PureConstraint.make_eq(sv,Value makeStr strLiteral, loc))}))
                  .addConstraint(LocalConstraint(valueReg,hc.snk, None)) ::  //And transfer whatever constraints we had on that heap cell to the value being written here.
                  //SECOND CASE: Assert properties don't match, leave heap constraint untouched
                  prop.fold({_ => Nil}, {sv => st.addConstraint(PureConstraint.make_diseq(sv, Value makeStr strLiteral, loc))::Nil})
              }
            case (stores,_) => stores
          }
          val proto_constraints_processed = ((stores_explicitHeapConstraintsProcessed map {_.dropConstraints(_.isInstanceOf[ProtoConstraint])}) /: store.protoConstraints.groupBy {
            _.prop
          }) { case (acc_stores, (prop, protos)) =>
            acc_stores flatMap { st =>
              val S1: Iterable[AbstrStore] = prop.fold(
                { strProp => if (strProp == strLiteral) Nil else Some(st addConstraints protos) }, { varProp => Some(st addConstraints protos addConstraint PureConstraint.make_diseq(Value makeStr strLiteral, varProp, loc)) }
              )
              val S2 = ((prop.fold(
                { strProp => if (strProp == strLiteral) Some(st) else None }, { varProp => Some(st addConstraint PureConstraint.make_eq(Value makeStr strLiteral, varProp, loc)) }
              ): Iterable[AbstrStore]) /: protos) { (stores, proto) =>
                val doesnt_flow = stores map { st =>
                  st addConstraint (proto addUpperBound st.getOrCreateSymbolicVar(rcvrReg))
                }
                val flows = if (proto.parent.isEmpty) Nil
                else stores map { st =>
                  val res_with_valueReg_bound =
                    st.addConstraint(proto.addVarWithProp(proto.parent.get))
                      .addConstraint(LocalConstraint(rcvrReg, proto.parent.get, None))
                      .withLocalBinding(valueReg)
                  res_with_valueReg_bound addConstraint HeapConstraint(Right(proto.parent.get), prop, res_with_valueReg_bound.getSymbolicVar(valueReg).get)
                }

                flows ++ doesnt_flow
              }
              S1 ++ S2
            }
          }

          (proto_constraints_processed /: store.localConstraints.filter {_.src == Variable(strLiteral, getScopeFn(strLiteral, loc))}) { (acc_stores, currLocal) =>
            acc_stores flatMap { currStore =>
              val rcvrSV = currStore.getSymbolicVar(rcvrReg).get
              val s1 = {
                val temp_s1 = currStore withLocalBinding Variable("this", loc)
                val this_var = temp_s1.getSymbolicVar(Variable("this", loc)).get
                temp_s1 addConstraint PureConstraint.make_diseq(this_var, rcvrSV, loc)
              }
              val s2 = {
                val temp_s2 = currStore dropConstraint currLocal withLocalBinding Variable("this", loc)
                val this_var = temp_s2.getSymbolicVar(Variable("this", loc)).get
                temp_s2.addConstraint(LocalConstraint(valueReg, currLocal.snk, None))
                  .addConstraint(ProtoConstraint(this_var, Some(rcvrSV), Left(strLiteral), varsWithProp = Set(rcvrSV)))
              }
              Seq(s1,s2)
            }
          }
      }
    } map {st =>
      st.dropConstraints({
        case lc:LocalConstraint => ! st.constrains(lc.snk)
        case _ => false
      })
    }
  }
  def write_var(variable : Variable, valueReg : Register, store : AbstrStore) : Iterable[AbstrStore] = {
    store.getLocalBinding(variable) match {
      case Some(local) =>
        Some(
          store dropConstraint local
                addConstraint LocalConstraint(valueReg, local.snk, None)
        )
      case _ => Some(store) //the variable being written to is unconstrained; leave store unchanged
    }
  }

  /**
    * Process a variable write
    *
    * @param store initial store
    * @param loc   location at which write occurs
    * @param lhs   symbolic variable being written to
    * @param rhs   value being written to that symbolic variable
    * @return Some(resulting store) or None (if the write refutes a constraint)
    */
  def writePure(store: AbstrStore, loc: ProgramLocation, lhs: SymbolicVar, rhs: PureExpr, forwards : Forwards): Option[AbstrStore] = {
    val opt_abstr_store = ((Some(store): Option[AbstrStore]) /: store.constraints) {
      case (opt_store, pure: PureConstraint) =>
        opt_store flatMap { st =>
          val pureWithWrite = pure.subPure(lhs, rhs)
          if (!pureWithWrite.satisfiable(forwards)) None
          else if (pureWithWrite.variables.isEmpty) Some(st.dropConstraint(pure))
          else Some(st.dropConstraint(pure).addConstraint(pureWithWrite))
        }
      case (opt_store, hc@HeapConstraint(src, Right(prop), snk)) if prop == lhs =>
        val strProp = PureBinOp(rhs, BinaryOperatorNode.Op.ADD, Value makeStr "", loc).toAbstractVal(forwards) // use TAJS for string coercion
        if (!strProp.isMaybeSingleStr) {
          opt_store map { st =>
            val freshVar = st.getFreshVar
            st.dropConstraint(hc).addConstraint(HeapConstraint(src, Right(freshVar), snk)).addConstraint(PureConstraint.make_eq(freshVar, rhs, loc))
          }
        } else {
          opt_store map { st => st.dropConstraint(hc).addConstraint(HeapConstraint(hc.rcvr, Left(strProp.getStr), hc.snk)) }
        }
      case (opt_store, pc@ProtoConstraint(child, parent, Right(prop), ubs, kps, vwp)) if prop == lhs =>
        val strProp = PureBinOp(rhs, BinaryOperatorNode.Op.ADD, Value makeStr "", loc).toAbstractVal(forwards) // use TAJS for string coercion
        if (!strProp.isMaybeSingleAllocationSite) {
          opt_store map { st =>
            val freshVar = st.getFreshVar
            st.dropConstraint(pc).addConstraint(ProtoConstraint(child, parent, Right(freshVar), ubs, kps, vwp)).addConstraint(PureConstraint.make_eq(freshVar, rhs, loc))
          }
        } else {
          opt_store map { st =>
            st.dropConstraint(pc).addConstraint(ProtoConstraint(child, parent, Left(strProp.getStr), ubs, kps, vwp)) }
        }
      case (opt_store, _) => opt_store
    }
    store match {
      case s : SetQueryAbstrStore => opt_abstr_store map {st => SetQueryAbstrStore(st.toSet, s.trackedValue.substitute(lhs,rhs))}
      case _ => opt_abstr_store
    }
  }

  /**
    * @param beginLoc ProgramLocation of loop entry
    * @param f forwards analysis api
    * @return disjunction of abstract stores (one with each possible loop context)
    */
  def makeStoresWithLoopCtx(beginLoc : ProgramLocation, f : Forwards, stores : Iterable[AbstrStore]) : Set[AbstrStore] = {
    assert(beginLoc.getNode.isInstanceOf[BeginForInNode])
    val beginNode = beginLoc.getNode.asInstanceOf[BeginForInNode]
    val objectReg = Register(beginNode.getObjectRegister, beginLoc.getNode.getBlock.getFunction)
    val objects : Set[ObjectLabel] = f.get(beginLoc, objectReg).getObjectLabels.toSet
    def makePropSets(definiteProperties : List[String], maybeProperties : List[String]):List[List[String]] = {
      (List(definiteProperties) /: (maybeProperties filterNot definiteProperties.contains)) {(acc,curr) => acc ++ (acc map (curr :: _)) }
    }
    objects flatMap { obj =>
      val properties : Properties = f.getForInProperties(beginLoc, obj)
      val props = makePropSets(properties.getDefiniteProperties.toList, properties.getMaybeProperties.toList)
      props flatMap { p =>
        stores map { st =>
          Executor.testTimeout()
          st.withLocalBinding(objectReg)
            .addConstraint(PureConstraint.make_eq(st.getOrCreateSymbolicVar(objectReg), Value.makeObject(obj), beginLoc))
            .addConstraint(ForInLoopCtxConstraint(beginNode, p))
        }
      }
    }
  }
}
