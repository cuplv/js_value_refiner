package edu.colorado.plv.js_value_refiner.constraint

import edu.colorado.plv.js_value_refiner.SymbolicVar


trait Constraint {
  def variables : Set[SymbolicVar]
  def substitute(oldV : SymbolicVar, newV : SymbolicVar) : Constraint
}
