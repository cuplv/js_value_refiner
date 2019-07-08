package edu.colorado.plv.js_value_refiner.constraint

import edu.colorado.plv.js_value_refiner.SymbolicVar
import edu.colorado.plv.js_value_refiner.memory.ProgramVar
import dk.brics.tajs.flowgraph.Function

case class LocalConstraint(src : ProgramVar, snk : SymbolicVar, closure: Option[(SymbolicVar, Function)]) extends Constraint{
  override def variables = closure match {case None => Set(snk) ; case Some(cl) => Set(snk, cl._1)}
  override def toString = s"$src${closure match {
    case None => ""
    case Some(cl) => s"@closure(${cl._1})"
  }} |-> $snk"
  override def substitute(oldV : SymbolicVar, newV : SymbolicVar) : Constraint = {
    def sub: SymbolicVar => SymbolicVar = { sv => if (sv == oldV) newV else sv }
    LocalConstraint(src, sub(snk), closure map {case (sv,fn) => sub(sv) -> fn})
  }
}
