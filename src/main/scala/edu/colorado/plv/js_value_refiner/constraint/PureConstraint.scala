package edu.colorado.plv.js_value_refiner.constraint

import dk.brics.tajs.lattice.Value
import edu.colorado.plv.js_value_refiner.{SymbolicVar, Util}
import dk.brics.tajs.flowgraph.jsnodes.BinaryOperatorNode.{Op => BinOp}
import dk.brics.tajs.flowgraph.jsnodes.UnaryOperatorNode.{Op => UnOp}
import edu.colorado.plv.value_refiner.AbstractValue
import forwards_backwards_api.{Forwards, ProgramLocation}

trait PureExpr {
  val variables : Set[SymbolicVar]
  def substitute(oldE : SymbolicVar, newE : PureExpr) : PureExpr
  def toAbstractVal(f : Forwards, knownVals : Map[SymbolicVar,Value] = Map()) : Value
  /** Helper function: strips an expression of top-level logical negations, returning the number of negations removed and the base expression */
  val negationsAndBase : (Int, PureExpr) = (0, this)
}


case class PureVar(v : SymbolicVar) extends PureExpr {
  override val variables = Set(v)
  override val toString = v.toString
  override def substitute(oldE : SymbolicVar, newE : PureExpr) : PureExpr =
    if(this.v == oldE) newE else this
  override def toAbstractVal(f : Forwards, knownVals : Map[SymbolicVar,Value]) : Value =
    knownVals.getOrElse(v, AbstractValue.top_non_obj)
}
case class PureVal(v : Value) extends PureExpr {
  override val variables = Set[SymbolicVar]()
  override val toString = v.toString
  override def substitute(oldE : SymbolicVar, newE : PureExpr) = this
  override def toAbstractVal(f : Forwards, knownVals : Map[SymbolicVar,Value]) : Value = v
}
case class PureBinOp(l : PureExpr, op : BinOp, r : PureExpr, loc : ProgramLocation) extends PureExpr {
  override val variables = l.variables union r.variables
  override val toString = s"($l ${Util.opToString(op)} $r)"
  override def substitute(oldE : SymbolicVar, newE : PureExpr) : PureExpr =
    PureBinOp(l.substitute(oldE,newE),op,r.substitute(oldE,newE), loc)
  override def toAbstractVal(f : Forwards, knownVals : Map[SymbolicVar,Value]) : Value =
    f.binop(loc, l.toAbstractVal(f, knownVals), op, r.toAbstractVal(f, knownVals))
}
case class PureUnOp(op : UnOp, expr : PureExpr, loc : ProgramLocation) extends PureExpr {
  override val variables = expr.variables
  override val toString = s"${Util.opToString(op)}$expr"
  override def substitute(oldE : SymbolicVar, newE : PureExpr) : PureExpr =
    PureUnOp(op,expr.substitute(oldE,newE), loc)
  override def toAbstractVal(f : Forwards, knownVals : Map[SymbolicVar,Value]) : Value =
    f.unop(loc,op,expr.toAbstractVal(f,knownVals))
  override val negationsAndBase = {
    val (subExprNegs, subExprBase) = expr.negationsAndBase
    op match {
      case UnOp.NOT => (1 + subExprNegs, subExprBase)
      case _ => (subExprNegs, subExprBase)
    }
  }
}

object PureConstraint {
  def    make_eq(v1 : PureExpr, v2 : PureExpr, loc : ProgramLocation) : PureConstraint = makeConstraint(v1,v2,true,  loc)
  def make_diseq(v1 : PureExpr, v2 : PureExpr, loc : ProgramLocation) : PureConstraint = makeConstraint(v1,v2,false, loc)
  private def makeConstraint(v1 : PureExpr, v2 : PureExpr, asserting : Boolean, loc : ProgramLocation) : PureConstraint = (v1,v2) match {
    case (PureVal(v),expr) => PureConstraint(expr,v,asserting)
    case (expr,PureVal(v)) => PureConstraint(expr,v,asserting)
    case _ => PureConstraint(PureBinOp(v1,BinOp.EQ,v2, loc), Value makeBool true, asserting)
  }
}

/**
 * Pure type constraint between a symbolic expression and a TAJS abstract value
 * If asserting,  interpreted as "[[lhs]] : [[rhs]]" or, equivalently "[[lhs]] \meet [[rhs]] != _|_"
 * If !asserting, the constraint must _not_ hold
 */
case class PureConstraint(lhs : PureExpr, rhs : Value, asserting:Boolean) extends Constraint {
  override def variables = lhs.variables
  override val toString = {
    val constraintBody =
      if (rhs == (Value makeBool true)) s"$lhs"
      else if (rhs == (Value makeBool false)) s"!($lhs)"
      else s"$lhs == $rhs"
    Console.GREEN + (if(asserting) constraintBody else s"!($constraintBody)")  + Console.RESET
  }
  override def substitute(oldV : SymbolicVar, newV : SymbolicVar) : Constraint = subPure(oldV,newV)
  def subPure(oldV : SymbolicVar, newE : PureExpr) : PureConstraint =
    PureConstraint(lhs.substitute(oldV,newE),rhs,asserting)
  def satisfiable(f : Forwards, knownVals : Map[SymbolicVar,Value] = Map()) : Boolean = {
    val lhsVal = lhs.toAbstractVal(f, knownVals)
    if(asserting)
      lhsVal.isMaybe(rhs) || (lhsVal.equals(AbstractValue.top_non_obj) && rhs.isMaybeObject) // concretization of lhs intersects concretization of rhs
    else
      !(lhsVal.join(rhs) == rhs) // concretization of lhs is NOT a subset of concretization of rhs

  }
}
