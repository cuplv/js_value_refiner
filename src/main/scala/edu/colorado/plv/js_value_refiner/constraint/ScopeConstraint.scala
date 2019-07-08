package edu.colorado.plv.js_value_refiner.constraint

import edu.colorado.plv.js_value_refiner.SymbolicVar
import dk.brics.tajs.flowgraph.Function

/** Asserts that [[sv]] is (resp. isn't, if ![[asserting]])an instance of [[decl_fn]] that is declared before leaving [[scope_fn]].  Used to track closures during the backwards analysis.
  *
  * Created by benno on 5/10/17.
  */
case class ScopeConstraint(sv: SymbolicVar, decl_fn: Function, scope_fn: Function, asserting: Boolean) extends Constraint{
  override def variables: Set[SymbolicVar] = Set(sv)

  override def substitute(oldV: SymbolicVar, newV: SymbolicVar): Constraint = if(sv == oldV) ScopeConstraint(newV, decl_fn, scope_fn, asserting) else this

  override def toString : String = s"Scope($sv:$decl_fn)${if(asserting) "=" else "!"}=$scope_fn"
}
