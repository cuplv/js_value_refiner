package edu.colorado.plv.js_value_refiner

import forwards_backwards_api.ProgramLocation
import dk.brics.tajs.flowgraph.{Function => TAJSFunction}
import dk.brics.tajs.Main.{run, init => tajsInit, reset => tajsReset}
import dk.brics.tajs.lattice.Value
import edu.colorado.plv.js_value_refiner.constraint.LocalConstraint
import edu.colorado.plv.js_value_refiner.memory.{Register, Variable}

import scala.collection.mutable.{MutableList => MList, Set => MSet}
import scala.collection.JavaConversions._
import scala.collection.immutable.Stack
import scala.language.postfixOps

object Executor {
  var startTime = System.currentTimeMillis();
  def testTimeout() = if(System.currentTimeMillis - startTime >= Options.TIMEOUT) {debug(s"Timing out; witnessed values so far:") ; throw new Executor.TimeoutException}

  class TimeoutException extends Exception

  def apply(src : String, logging : Boolean = true) : Executor = {
    tajsReset()
    Options.DEBUG=logging
    val analysis = tajsInit(Array(src), null)
    run(analysis)
    new Executor(analysis.getForwards)
  }

  /** Used for testing, to dispatch queries at some particular line*/
  def canRefuteFromLine(lineNum : Int, src : String, query : RefinementConstraint, logging : Boolean = false) : Boolean = {
    Options.DEBUG=logging
    dk.brics.tajs.options.Options.get.disableControlSensitivity
    dk.brics.tajs.options.Options.get.enableTest
    val analysis = tajsInit(Array(src), null)
    run(analysis)
    debug(analysis.getSolver.getFlowGraph)
    val lastNodeAtLine = {
      analysis.getSolver.getFlowGraph//get flow graph
        .getFunctions.flatMap { _.getBlocks.flatMap {_.getNodes}}//get all nodes from flowgraph
        .filter {n => n.getSourceLocation.getLineNumber == lineNum && n.getSourceLocation.getLocation.getProtocol != "tajs-host-env"} //grab those on the right line
        .maxBy {_.getIndex}//choose the last node from that line
    }
    val contexts = analysis.getSolver.getAnalysisLatticeElement.getStates(lastNodeAtLine.getBlock).keySet.iterator()
    contexts.forall { ctx =>
      val loc = new ProgramLocation(lastNodeAtLine, ctx)
        new Executor(analysis.getForwards).canRefute(
          DisjunctState(loc, Set(query.toConstraints(loc)), Stack(), Stack())
        )
    }
  }

  /** Used for testing, to check whether we can prove a program doesn't terminate without error */
  def canRefuteFinalState(src : String, logging : Boolean = false) : Boolean = {
    Options.DEBUG=logging
    dk.brics.tajs.options.Options.get.disableControlSensitivity
    dk.brics.tajs.options.Options.get.enableTest
    val analysis = tajsInit(Array(src), null)
    run(analysis)
    debug(analysis.getSolver.getFlowGraph)
    val exitBlock = analysis.getSolver.getFlowGraph.getMain.getOrdinaryExit
    val exitContext = analysis.getSolver.getAnalysisLatticeElement.getStates(exitBlock).keySet.iterator.next
    new Executor(analysis.getForwards).canRefute(
      DisjunctState(new ProgramLocation(analysis.getSolver.getFlowGraph.getMain.getOrdinaryExit.getNodes.head, exitContext), Set(AbstrStore()), Stack(), Stack())
    )
  }

  /** Used for testing refinement queries, to refine the possible values of a program variable from a given set of values at a particular line  */
  def refineVarFromLine(pv : Either[String,Int], src : String, lineNum : Int, logging : Boolean = false) : Set[Value] = {
    Options.DEBUG=logging
    dk.brics.tajs.options.Options.get.enablePropagateDeadFlow()
    dk.brics.tajs.options.Options.get.disableControlSensitivity()
    dk.brics.tajs.options.Options.get.enableTest()
    val analysis = tajsInit(Array(src), null)
    run(analysis)
    debug(analysis.getSolver.getFlowGraph)
    val lastNodeAtLine = {
      analysis.getSolver.getFlowGraph//get flow graph
        .getFunctions.flatMap { _.getBlocks.flatMap {_.getNodes}}//get all nodes from flowgraph
        .filter {n => n.getSourceLocation.getLineNumber == lineNum && n.getSourceLocation.getLocation.getProtocol != "tajs-host-env"} //grab those on the right line
        .maxBy {_.getIndex}//choose the last node from that line
    }
    val contexts = analysis.getSolver.getAnalysisLatticeElement.getStates(lastNodeAtLine.getBlock).keySet.iterator()
    contexts.map { ctx =>
      val loc = new ProgramLocation(lastNodeAtLine, ctx)
      new Executor(analysis.getForwards).refine(
        Set(SetQueryAbstrStore(Set(LocalConstraint(pv.fold({s => Variable(s,getScopeFn(s,loc))}, {v => Register(v,loc)}), SymbolicVar(0), None)),SymbolicVar(0))),
        loc
      )
    }.foldLeft(Set[Value]()){ _ union _.toSet }
  }

  /** Used for testing Set Queries, to refine the possible values of a program variable from a given set of values at the program's final state */
  def refineVarFromFinalState(pv : Either[String,Int], src : String,logging : Boolean = false) : Set[Value] = {
    Options.DEBUG=logging
    dk.brics.tajs.options.Options.get.disableControlSensitivity
    dk.brics.tajs.options.Options.get.enableTest
    val analysis = tajsInit(Array(src), null)
    run(analysis)
    verbose(analysis.getSolver.getFlowGraph)
    val exitBlock = analysis.getSolver.getFlowGraph.getMain.getOrdinaryExit
    val exitContext = analysis.getSolver.getAnalysisLatticeElement.getStates(exitBlock).keySet.iterator.next
    val loc = new ProgramLocation(analysis.getSolver.getFlowGraph.getMain.getOrdinaryExit.getNodes.head, exitContext)
    new Executor(analysis.getForwards).refine(
      Set(SetQueryAbstrStore(Set(LocalConstraint(pv.fold({s => Variable(s,exitBlock.getFunction)}, {v => Register(v,loc)}),SymbolicVar(0), None)),SymbolicVar(0))),
        loc
    ).toSet
  }
}


class Executor(val forwards : AssumptionTrackingForwards) {

  private val transfers = new BackwardsTransfer(forwards)

  private val workList: MSet[DisjunctState] = MSet()

  /** Used for set queries, to track which values have been seen in the backwards execution */
  private val witnessedValues: MSet[Value] = MSet()

  /** [[functionOrder]] is used for workList prioritization.
    * We prioritize [[Function]]s by the order in which this [[Executor]] encounters them.
    * */
  private val functionOrder: MList[TAJSFunction] = MList()

  /**
   * @param ds1
   * @param ds2
   * @return 1 if ds1 has workList priority over ds2, -1 if ds2 has priority over ds1, and 0 if they have equal priority
   *         if 0 is returned, it's guaranteed that ds1 and ds2 are at the same program location with the same call stack
   */
  private def priority(ds1: DisjunctState, ds2: DisjunctState): Int = {
    ds1.callStack.size - ds2.callStack.size match {
      case diff if diff > 0 => 1
      case diff if diff < 0 => -1
      case _ => // ds1 and ds2 have the same callStack depth, so compare by function order
        functionOrder.indexOf (ds2.function) - functionOrder.indexOf (ds1.function) match {
          case diff if diff > 0 => - 1
          case diff if diff < 0 => 1
          case _ => // ds1 and ds2 are from the same function, so compare by block
            ds1.block.getTopologicalOrder - ds2.block.getTopologicalOrder match {
              case diff if diff > 0 => 1
              case diff if diff < 0 => - 1
              case _ => //ds1 and ds2 are from the same block, so compare by node index
                ds1.loc.getNode.getIndex - ds2.loc.getNode.getIndex match {
                  case diff if diff > 0 => 1
                  case diff if diff < 0 => - 1
                  case _ => // same syntactic location, so just choose arbitrarily if they don't have the same loop context and callstack
                    if (ds1.callStack == ds2.callStack && ds1.containingLoopInitialStores == ds2.containingLoopInitialStores && ds1.loc.getContexts == ds2.loc.getContexts) 0 else 1
                }
            }
        }
    }
  }
  /**
    * Adds a disjunct state to the worklist, maintaining the invariant that no two disjunct states in the worklist
    * share the same location by merging {@param ds} with a preexisting state if one exists.
    *
    * @param ds DisjunctState to add to workList
    */
  private def addToWorkList(ds: DisjunctState): Unit = {
    workList find { priority(_, ds) == 0 } match {
      case None =>
        workList add ds
      case Some(ds_prime) =>
        workList remove ds_prime
        workList add DisjunctState(ds.loc, ds.stores union ds_prime.stores, ds.callStack, ds.containingLoopInitialStores)
    }
  }

  /**
   * Pop the highest-priority element from the [[workList]] and step it backwards over a basic block.
   *
   * Mutates the [[workList]].
   */
  def step() : Unit = {
    require(workList.nonEmpty, "Can't take a step if worklist is empty.")
    // Find DisjunctState from workList with maximal priority
    val state_to_process = workList.tail.foldLeft(workList.head) {(ds1,ds2) => priority(ds1,ds2) match {
      case 1 => ds1
      case -1 => ds2
      case 0 => throw new IllegalStateException("Two disjunct states in worklist at same location")
    }}

    workList remove state_to_process

    val t_start = System.currentTimeMillis()
    val transfer_result = transfers.transfer(state_to_process)
    val t_end = System.currentTimeMillis

    val postcondition_states : Int = state_to_process.stores size
    val  precondition_states : Int = transfer_result map {_.stores.size} sum

    val transfer_debug_color = precondition_states/postcondition_states match {
      case x if x >= 5 => Console.RED    // Branching factor >= 5
      case x if x >  1 => Console.YELLOW // Branching factor >  1
      case x           => Console.GREEN  // Branching factor <= 1
    }
    verbose(s"${state_to_process.loc.getNode.getIndex}:${state_to_process.loc} transfer function; preds: ${forwards.getPredecessors(state_to_process.loc).map{_.getNode.getIndex}}\t\t" +
      transfer_debug_color + s"maps $postcondition_states stores to $precondition_states." + Console.RESET  +
      s"\t\tin ${t_end-t_start}ms")
    //      s"\t\t${workList.map{_.stores.size}.sum} unaffected stores in worklist at locations ${workList.map{_.loc.getNode.getIndex}}")

    //NOTE(Benno): Change this condition to print more detailed information about particular transfers.
    //  For more granular debugging information, it is often necessary to instrument lower-level functions e.g.:
    //    - transfers themselves (BackwardsTransfer.scala)
    //    - native models (Natives.scala)
    //    - constraint solver (AbstrStore.scala)
    if(false)
      verbose("Precondition States:\n\t" + transfer_result.flatMap{_.stores}.mkString("\n\t") +
        "\nPostcondition States:\n\t" + state_to_process.stores.mkString("\n\t") + "\n")

    // If we refute in a loop body, backtrack to the loop head and don't enter the loop
    if(transfer_result.isEmpty && state_to_process.containingLoopInitialStores.nonEmpty) {
      val loopInitState = state_to_process.containingLoopInitialStores.head
      addToWorkList(DisjunctState(loopInitState._1, Set(loopInitState._2),state_to_process.callStack,state_to_process.containingLoopInitialStores))
    }

    transfer_result foreach {ds =>
      if(!(functionOrder contains ds.function)) functionOrder += ds.function
      val stores = ds.stores.filter {
        case s : SetQueryAbstrStore =>
          s.getDefiniteValue(state_to_process.loc, ds.loc, forwards) match {
            case None if isEntry(forwards,ds.loc) && s.isSatisfiable(forwards,ds.loc) => witnessedValues += Value.makeUndef ; false
            case None => true
            case Some(v) if witnessedValues containsAll v => false
            case Some(v) if Options.STOPPING_CRITERION == Options.DefiniteValueFound =>
              witnessedValues.addAll(v)
              false
            case Some(v) if Options.STOPPING_CRITERION == Options.FunctionEntrypoint =>
              if(ds.loc.getNode.getBlock.isEntry && forwards.getPredecessors(ds.loc).isEmpty && ds.callStack.isEmpty && s.isSatisfiable(forwards, ds.loc)) {
                witnessedValues.addAll(v)
                false
              } else true
            case Some(v) if Options.STOPPING_CRITERION == Options.ProgramEntrypoint && s.isSatisfiable(forwards, ds.loc) =>
              if(isEntry(forwards,ds.loc)) {
                witnessedValues.addAll(v)
                false
              } else true
          }
        case _ => true
      }
      if(stores nonEmpty) addToWorkList(DisjunctState(ds.loc,stores,ds.callStack, ds.containingLoopInitialStores))
    }
  }

  /** Main entrypoint to Executor.  Mutates the [[workList]].
    * @return true iff js_value_refiner can soundly refute the condition specified in intialQuery
    */
  def canRefute(initialQuery: DisjunctState, timeoutMillis : Int = Options.TIMEOUT): Boolean = {
    val startTime = System.currentTimeMillis
    if (isEntry(forwards,initialQuery.loc) &&
        validateEntry(initialQuery)) return false

    require(workList.isEmpty)
    workList add initialQuery

    while (true) {
      //If all paths have reached a contradiction and been dropped, refute
      if (workList.isEmpty) return true

      //Can't refute if we time out.
      if(System.currentTimeMillis - startTime >= timeoutMillis) {debug(s"Timing out; witnessed values so far: $witnessedValues") ; throw new Executor.TimeoutException}

      val previous_WL = workList.clone
      step()


      //If a path has reached an entrypoint without contradiction, can't refute
      if ((workList -- previous_WL) exists { ds =>
        isEntry(forwards,ds.loc) && validateEntry(ds)
      }) return false
    }
    sys.error("This is unreachable - the only ways out of the while-loop are return statements")
  }

  /**
    * Refines the trackedValue of a SetQueryAbstrStore to as small a set of unrefutable values as possible
    */
  def refine(query : Iterable[SetQueryAbstrStore],
             loc : ProgramLocation,
             timeoutMillis : Int = Options.TIMEOUT) : java.util.Set[Value] = {
    require(workList.isEmpty)
    require(witnessedValues.isEmpty)

    Executor.startTime = System.currentTimeMillis()
    workList add DisjunctState(loc, query.toSet[AbstrStore], Stack(), Stack())

    while(true) {
      val elapsedTime = System.currentTimeMillis() - Executor.startTime
      if(elapsedTime >= timeoutMillis) {
        verbose(s"Timing out; witnessed values so far: $witnessedValues")
        throw new Executor.TimeoutException
      }
      step()
      if(workList.isEmpty){
        verbose(s"ELAPSED TIME: $elapsedTime")
        return witnessedValues
      }
    }
    sys.error("This is unreachable - the only ways out of the while loop are exceptions/returns")
  }

  /**
   * Checks whether a disjunct state that has reached the main function's entry block is contradiction-free.
   * Removes ds from [[workList]] regardless of satisfiability
   *   - if it is satisfiable, the backwards analysis is done
   *   - if it isn't satisfiable, then we've hit a contradiction and can stop searching this path
 *
   * @param ds Asssumed to be (1) in the workList and (2) at an entrypoint.
   * @return true iff ds is contradiction free
   */
  def validateEntry(ds: DisjunctState): Boolean = {
    require(isEntry(forwards, ds.loc))
    workList remove ds
    ds.isSatisfiable(forwards)
  }

}
