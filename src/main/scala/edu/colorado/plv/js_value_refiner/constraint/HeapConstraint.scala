package edu.colorado.plv.js_value_refiner.constraint

import dk.brics.tajs.lattice.Value
import edu.colorado.plv.js_value_refiner.SymbolicVar

/**
 * Value refiner Separation Logic constraint
 *
 * @param rcvr
 * @param prop
 * @param snk Constrained value
 */
case class HeapConstraint(rcvr : Either[Value,SymbolicVar], prop : Either[String,SymbolicVar], snk : SymbolicVar) extends Constraint{
  assert(rcvr.fold({value => !value.isMaybePrimitiveOrSymbol && value.getObjectLabels.size == 1},{_ => true}), "HeapConstraint receiver must be a singleton object value")
  override def variables = rcvr.right.toOption ++ prop.right.toOption ++ Some(snk) toSet
  override def toString = s"${rcvr.fold({x=>x},{_.toString})}.${prop.fold({x=>x},{_.toString})} |-> $snk"
  override def substitute(oldV : SymbolicVar, newV : SymbolicVar) : Constraint =
    HeapConstraint(if (rcvr == Right(oldV)) Right(newV) else rcvr,
                   if (prop == Right(oldV)) Right(newV) else prop,
                   if (snk == oldV)         newV        else snk)
}
