package edu.colorado.plv.js_value_refiner

import dk.brics.tajs.flowgraph.jsnodes.BinaryOperatorNode.{Op => BinOp}
import dk.brics.tajs.lattice.Value
import dk.brics.tajs.util.AnalysisException
import edu.colorado.plv.js_value_refiner.constraint._
import edu.colorado.plv.js_value_refiner.memory.ProgramVar
import edu.colorado.plv.value_refiner.AbstractValue
import forwards_backwards_api.{Forwards, ProgramLocation}

import scala.language.postfixOps

object AbstrStore {
  def apply(constraints : Constraint*) : AbstrStore = AbstrStore(constraints toSet)
}

case class AbstrStore(constraints : Set[Constraint], canonicalized:Boolean = false) extends Iterable[Constraint]{

  lazy val localConstraints   : Iterable[LocalConstraint]        = constraints filter {_.isInstanceOf[LocalConstraint]       } map {_.asInstanceOf[LocalConstraint]}
  lazy val heapConstraints    : Iterable[HeapConstraint]         = constraints filter {_.isInstanceOf[HeapConstraint]        } map {_.asInstanceOf[HeapConstraint]}
  lazy val pureConstraints    : Iterable[PureConstraint]         = constraints filter {_.isInstanceOf[PureConstraint]        } map {_.asInstanceOf[PureConstraint]}
  lazy val protoConstraints   : Iterable[ProtoConstraint]        = constraints filter {_.isInstanceOf[ProtoConstraint]       } map {_.asInstanceOf[ProtoConstraint]}
  lazy val loopConstraints    : Iterable[ForInLoopCtxConstraint] = constraints filter {_.isInstanceOf[ForInLoopCtxConstraint]} map {_.asInstanceOf[ForInLoopCtxConstraint]}
  lazy val closureConstraints : Iterable[ClosureConstraint]      = constraints filter {_.isInstanceOf[ClosureConstraint]     } map {_.asInstanceOf[ClosureConstraint]}
  lazy val scopeConstraints   : Iterable[ScopeConstraint]        = constraints filter {_.isInstanceOf[ScopeConstraint]       } map {_.asInstanceOf[ScopeConstraint]}

  def canonicalize(f : Forwards, loc : ProgramLocation) : AbstrStore = {
    if(canonicalized) return this
    // get symbolic variable equivalence classes that arise from heap and local constraints
    val equiv_classes = getSymVarEquivClasses

    //Helper functions to update constraints
    def canon: SymbolicVar => SymbolicVar = { sv =>
      equiv_classes find {
        _ contains sv
      } match {
        case Some(equiv_class) => equiv_class.head
        case None => sv
      }
    }
    def canonPure: PureExpr => PureExpr = {
      case PureBinOp(l, op, r, binop_loc) =>
        val binop = PureBinOp(canonPure(l), op, canonPure(r), binop_loc)
        if(binop.variables.isEmpty) binop.toAbstractVal(f)
        else binop
      case PureUnOp(op, expr, unop_loc) =>
        val unop = PureUnOp(op, canonPure(expr), unop_loc)
        if(unop.variables.isEmpty) unop.toAbstractVal(f)
        else unop
      case p: PureVal => p
      case PureVar(v) => PureVar(canon(v))
    }
    //collapse all equivalence classes of aliased symbolic variables.
    val vars_canonicalized = map {
      case PureConstraint(lhs, rhs, a) => PureConstraint(canonPure(lhs), rhs, a)
      case LocalConstraint(src, snk, closure) => LocalConstraint(src, canon(snk), closure map {case (sv,fn) => canon(sv) -> fn})
      case HeapConstraint(Right(rcvr), prop, snk) => HeapConstraint(Right(canon(rcvr)), prop.fold({ x => Left(x) }, { x => Right(canon(x)) }), canon(snk))
      case HeapConstraint(rcvr, prop, snk) => HeapConstraint(rcvr, prop.fold({ x => Left(x) }, { x => Right(canon(x)) }), canon(snk))
      case ProtoConstraint(child, parent, prop, ubs, kps, vwp) => ProtoConstraint(
        canon(child),
        parent map canon,
        prop.fold({ x => Left(x) }, { x => Right(canon(x)) }),
        ubs map canon,
        kps map { case (k, v) => (canon(k), canon(v))},
        vwp map canon
      )
      case ClosureConstraint(cl1,cl2,a) => ClosureConstraint(canon(cl1),canon(cl2),a)
      case ScopeConstraint(sv,decl,scope,a) => ScopeConstraint(canon(sv),decl,scope,a)
      case l: ForInLoopCtxConstraint => l
    }

    // resolve any heap/proto constraint symbolic var properties whose string value can be determined
    val knownValues : Map[SymbolicVar,Value] = vars_canonicalized.pureConstraints.flatMap(getDefiniteValBinding)
      .groupBy{_._1}
      .map {case (sv,vals) => sv -> (vals map {_._2} reduce {_ meet _})}

    val knownStrValues : Map[SymbolicVar,String]= knownValues
      .filter{case (sv,value) => value.isDefinitelyStr && value.isMaybeSingleStr}
      .map   {case (sv,value) => sv -> value.getStr}

    val nativeProps = Natives.getNativeProperties(knownValues)

    AbstrStore((vars_canonicalized map {
      case HeapConstraint(rcvr,Right(propSV),snk) if knownStrValues.keySet contains propSV => HeapConstraint(rcvr, Left(knownStrValues(propSV)),snk)
      case ProtoConstraint(child,parent,Right(propSV),ubs,kps,vwp) if knownStrValues.keySet contains propSV =>
        ProtoConstraint(child,parent,Left(knownStrValues(propSV)),ubs,kps,vwp ++ nativeProps(knownStrValues(propSV)))
      case ProtoConstraint(child,parent,prop@Left(propStr),ubs,kps,vwp) => ProtoConstraint(child,parent,prop,ubs,kps,vwp ++ nativeProps(propStr))
      case x => x
    } filterNot {
      case PureConstraint(PureBinOp(l,BinOp.EQ,r,_),v,true) if v == (Value makeBool true) => l == r
      case pure:PureConstraint => pure.variables.isEmpty && pure.satisfiable(f)
      case c:ClosureConstraint => c.asserting && (c.cl1 == c.cl2)
      case _ => false
    }).toSet[Constraint], canonicalized=true)
  }

  def getDefiniteValBinding(pc : PureConstraint) : Option[(SymbolicVar,Value)] = {
    val equality_ops = Set(BinOp.EQ,BinOp.SEQ)
    val disequality_ops = Set(BinOp.NE,BinOp.SNE)
    val (negations, baseExpr) = pc.lhs.negationsAndBase
    val netPositive = (negations + (if(pc.asserting) 0 else 1)) % 2 == 0

    val res = baseExpr match {
      case PureVar(v) if netPositive && negations == 0 => Some(v -> pc.rhs) // if there are negations, the rhs is the boolean coerced value of v and not the actual value of v
      case PureBinOp(PureVar(v),op,PureVal(value),_) if (equality_ops contains op) && pc.rhs == Value.makeBool(netPositive) => Some(v -> value)
      case PureBinOp(PureVal(value),op,PureVar(v),_) if (equality_ops contains op) && pc.rhs == Value.makeBool(netPositive) => Some(v -> value)
      case PureBinOp(PureVar(v),op,PureVal(value),_) if (disequality_ops contains op) && pc.rhs == Value.makeBool(!netPositive) => Some(v -> value)
      case PureBinOp(PureVal(value),op,PureVar(v),_) if (disequality_ops contains op) && pc.rhs == Value.makeBool(!netPositive) => Some(v -> value)
      case _ => None
    }
    res
  }


  def isSatisfiable(f : Forwards, loc : ProgramLocation) : Boolean = // A store is satisfiable when:
    puresSatisfiable(f, loc) && // All of its pure constraints are satisfiable
      protosSatisfiable(f, loc) && // All of its prototype constraints are satisfiable
      (!isEntry(f, loc) || heapConstraints.forall(_.rcvr isRight)) && // If this is an entrypoint, all heap constraints have been resolved
      closureConstraints.forall {cc => cc.cl1 != cc.cl2 || cc.asserting} // All closure constraints are satisfiable

  /** Using heap and local constraints, generates all equivalence classes (of size > 1) of symbolic variables */
  def getSymVarEquivClasses : List[Set[SymbolicVar]] = {
    val heap_equiv_classes  : Iterable[Set[SymbolicVar]] =
      heapConstraints  groupBy {hc => (hc.prop,hc.rcvr)} filter {_._2.size > 1} map {_._2 map {_.snk} toSet}
    val local_equiv_classes : Iterable[Set[SymbolicVar]] =
      localConstraints groupBy {_.src}                   filter {_._2.size > 1} map {_._2 map {_.snk} toSet}
    val proto_equiv_classes : Iterable[Set[SymbolicVar]] =
      protoConstraints groupBy {pc => (pc.child,pc.prop,pc.upperBounds,pc.knownProtos)} filter {_._2.size > 1} map {_._2 flatMap {_.parent} toSet}

    (heap_equiv_classes ++ local_equiv_classes ++ proto_equiv_classes).foldLeft(Nil : List[Set[SymbolicVar]]) {(acc, curr) =>
      val(intersecting_classes, nonintersecting_classes) = acc.partition { equiv_class => (equiv_class intersect curr).nonEmpty }
      (curr /: intersecting_classes){_ union _} :: nonintersecting_classes
    }
  }

  @annotation.tailrec
  private def reducePures(pures : Iterable[PureConstraint], f : Forwards, loc : ProgramLocation) : Iterable[PureConstraint] = {
    val knownValues = pures.flatMap(getDefiniteValBinding).groupBy {_._1}
      .map {case (sv,vals) =>
        sv -> vals.map{_._2}.reduce {(v1,v2) =>
          try v1 meet v2 catch {case e : AnalysisException => debug(s"AnalysisException while applying meet (returning bottom):\nV1: $v1\nV2: $v2") ; debug(e) ; AbstractValue.bot}}}
    def reduceExpr : PureExpr => PureExpr = {
      case PureBinOp(l, op, r,binop_loc) =>
        val binop = PureBinOp(reduceExpr(l), op, reduceExpr(r),binop_loc)
        if(binop.op == BinOp.EQ && l == r) Value makeBool true
        else if (binop.variables.isEmpty) binop.toAbstractVal(f)
        else binop
      case PureUnOp(op, expr, unop_loc) =>
        val unop = PureUnOp(op, reduceExpr(expr), unop_loc)
        if (unop.variables.isEmpty) unop.toAbstractVal(f)
        else unop
      case p: PureVal => p
      case pv@PureVar(v) =>
        knownValues get v match {
          case Some(kv) => kv
          case _ => pv
        }
    }
    val reduced = pures.map {case PureConstraint(lhs,rhs,a) => PureConstraint(reduceExpr(lhs),rhs,a)}

    //Repeat until fixed point
    if(reduced == pures) reduced
    else reducePures(reduced, f, loc)
  }

  def puresSatisfiable(f : Forwards, loc : ProgramLocation) : Boolean = reducePures(pureConstraints, f, loc) forall {_.satisfiable(f)}

  def protosSatisfiable(f : Forwards, loc : ProgramLocation) : Boolean =
    if(isEntry(f,loc))
      protoConstraints forall { pc =>
        pc.parent match {
          case Some(parent) => pc.protoPathExists(pc.child, parent)
          case None => pc.satisfiable && heapConstraints.forall{hc => hc.rcvr != Right(pc.child) || hc.prop != pc.prop}
        }
      }
    else
      protoConstraints forall {_.satisfiable}


  def addConstraints(cs : Iterable[Constraint]) = (this /: cs) {_ addConstraint _}
  def addConstraint(c : Constraint) : AbstrStore = new AbstrStore(constraints + c)

  /** Drops all constraints satisfying predicate */
  def dropConstraints(predicate : Constraint => Boolean) : AbstrStore = filterNot( predicate )
  def dropConstraint(c : Constraint) : AbstrStore =
    if(constraints contains c)
      new AbstrStore (constraints - c)
    else
      throw new IllegalArgumentException("Can't remove a constraint that's not already in the Abstract Store")

  /**
   * @return A [[SymbolicVar]] whose index is greater than that of any [[SymbolicVar]] in this [[AbstrStore]]
   */
  def getFreshVar : SymbolicVar = {
    (SymbolicVar(0) /: (constraints flatMap {_.variables})) {(lowest_fresh, variable) =>
      variable match {
        case SymbolicVar(i) if i >= lowest_fresh.num => SymbolicVar(i+1)
        case _ => lowest_fresh
      }
    }
  }

  /**
   * @param s
   * @return the [[SymbolicVar]] bound to s by a constraint, if one exists
   */
  def getSymbolicVar(s : ProgramVar) : Option[SymbolicVar] = localConstraints find {_.src == s} map {_.snk}


  def withLocalBinding(v : ProgramVar) : AbstrStore = {
    if (this.exists { case LocalConstraint(`v`,_,_) => true ; case _ => false})
      this
    else
      this.addConstraint(LocalConstraint(v,getFreshVar,None))
  }

  def getLocalBinding(v : ProgramVar) : Option[LocalConstraint] = localConstraints find {_.src == v}

  def getOrCreateSymbolicVar(s : ProgramVar) : SymbolicVar =
    getSymbolicVar(s) match {
      case Some(sv) => sv
      case None => getFreshVar
    }

  def constrains( v : SymbolicVar ) : Boolean = // A store constrains a symbolic variable v when a constraint refers to it, unless that constraint is a simple x |-> v local constraint binding the symbolic variable to some program variable x
    exists{
      case LocalConstraint(src,snk,cl) => cl exists {_._1 == v}
      case c => c.variables contains v
    }


  override def iterator  = constraints.iterator

  override def toString = (localConstraints.toSeq ++ constraints.filterNot{_.isInstanceOf[LocalConstraint]}.toSeq)  map {c => s"($c)" } mkString(Console.RED + "{" + Console.CYAN,
                                                                    Console.RED + "∧" + Console.CYAN,
                                                                    Console.RED + "}" + Console.RESET)

  /** Take the least upper bound of two AbstrStores by ensuring their variables are disjoint and then unioning them */
  def meet(other : AbstrStore) : AbstrStore = {
    val leastFreshVarIndex : Int = getFreshVar.num
    def ensureFresh : SymbolicVar => SymbolicVar = {v => SymbolicVar(v.num + leastFreshVarIndex)}
    def ensurePropFresh(prop : Either[String,SymbolicVar]) : Either[String,SymbolicVar] = prop.fold(Left.apply, ensureFresh andThen Right.apply )
    def ensurePureFresh : PureExpr => PureExpr = {
      case v : PureVal       => v
      case PureVar(v)        => ensureFresh(v)
      case PureUnOp(op,e, loc)    => PureUnOp(op, ensurePureFresh(e), loc)
      case PureBinOp(l,op,r, loc) => PureBinOp(ensurePureFresh(l), op, ensurePureFresh(r), loc)
    }
    val otherWithDisjVars : Set[Constraint] = other.map {
      case LocalConstraint(src,snk,closure) => LocalConstraint(src, ensureFresh(snk), closure map {case (sv,fn) => ensureFresh(sv) -> fn})
      case HeapConstraint(Right(rcvr),prop,snk) => HeapConstraint(Right(ensureFresh(rcvr)), ensurePropFresh(prop), ensureFresh(snk))
      case HeapConstraint(rcvr,prop,snk) => HeapConstraint(rcvr, ensurePropFresh(prop), ensureFresh(snk))
      case c:ForInLoopCtxConstraint => c
      case ProtoConstraint(child, parent, prop, ubs, kps, vwp) =>
        ProtoConstraint(ensureFresh(child), parent map ensureFresh, ensurePropFresh(prop), ubs map ensureFresh,
                        kps map {case (x,y) => ensureFresh(x) -> ensureFresh(y)}, vwp map ensureFresh)
      case PureConstraint(lhs,rhs,a) => PureConstraint(ensurePureFresh(lhs),rhs,a)
    } toSet

    constraints union otherWithDisjVars
  }


  /** Take the greatest lower bound of two AbstrStores by taking their intersection*/
  def join(other : AbstrStore) : Iterable[AbstrStore] = Some(AbstrStore(this.collateVarsWith(other).toSet intersect other.toSet))

  /** Return this AbstrStore with all symbolic variables renamed so that they correspond to the same program variables as they do in other*/
  @annotation.tailrec
  final protected def collateVarsWith(other : AbstrStore) : AbstrStore = {
    (varMap.keySet intersect other.varMap.keySet) find {v => varMap(v) != other.varMap(v)} match {
      case Some(pv) if ! variables.contains(other.varMap(pv)) => // If this abstrstore doesn't use the symbolic variable other uses for pv
        substitute(varMap(pv), other.varMap(pv)).collateVarsWith(other)
      case Some(pv) => // if this abstrstore already uses the symbolic variable other uses for pv
        substitute(other.varMap(pv),getFreshVar).substitute(varMap(pv),other.varMap(pv)).collateVarsWith(other)
      case None => this
    }
  }
  lazy protected val varMap : Map[ProgramVar, SymbolicVar] = localConstraints map {lc => lc.src -> lc.snk} toMap
  lazy val variables : Set[SymbolicVar] = constraints flatMap {_.variables}

  def substitute(oldV : SymbolicVar, newV : SymbolicVar) : AbstrStore = constraints map {_.substitute(oldV,newV)}
}
