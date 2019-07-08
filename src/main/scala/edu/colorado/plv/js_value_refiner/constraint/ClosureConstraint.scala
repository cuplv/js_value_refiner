package edu.colorado.plv.js_value_refiner.constraint

import edu.colorado.plv.js_value_refiner.SymbolicVar

/** Asserts that [[cl1]] and [[cl2]] are the same(resp. different, if ![[asserting]]) instance of some function.  Used to track closure-scoped program variables.
  *
  * Created by benno on 5/10/17.
  */
case class ClosureConstraint(cl1: SymbolicVar, cl2: SymbolicVar, asserting:Boolean) extends Constraint{
  override def variables: Set[SymbolicVar] = Set(cl1,cl2)

  override def substitute(oldV: SymbolicVar, newV: SymbolicVar): Constraint =
    ClosureConstraint(
      if(cl1==oldV) newV else cl1,
      if(cl2==oldV) newV else cl2,
      asserting
    )

  override def toString: String =
    if(asserting) s"SameInstance($cl1,$cl2)"
    else          s"DiffInstance($cl1,$cl2)"
}
