package edu.colorado.plv.js_value_refiner.constraint

import dk.brics.tajs.flowgraph.jsnodes.BeginForInNode
import edu.colorado.plv.js_value_refiner.SymbolicVar

/**
  * Constrains the iteration context of a given for-in loop
  *
  * @param loopHead The BeginForInNode identifying the loop whose context is being restricted
  * @param propValues The set of property values by which the context-restriction is parameterized
  * @param currPropIdx The current loop iteration
  *
  */
case class ForInLoopCtxConstraint(loopHead : BeginForInNode, propValues : List[String], currPropIdx:Int = 0) extends Constraint {
  assert(propValues.groupBy(x=>x).forall{_._2.size == 1}) // No duplicate properties
  assert(currPropIdx < propValues.size) // Can't be on the nth iteration of a loop with fewer than n iterations
  override def variables = Set()
  override def toString = s"loop-has-prop($loopHead,$propValue,${propValues.mkString("{",",","}")})"
  override def substitute(oldV: SymbolicVar, newV: SymbolicVar) = this

  def propValue = propValues(currPropIdx)

  def next : Option[ForInLoopCtxConstraint] =
    if(currPropIdx+1 >= propValues.size) None
    else Some(ForInLoopCtxConstraint(loopHead,propValues,currPropIdx+1))
}