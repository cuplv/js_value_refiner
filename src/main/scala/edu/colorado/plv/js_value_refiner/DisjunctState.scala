package edu.colorado.plv.js_value_refiner

import edu.colorado.plv.js_value_refiner.constraint.Constraint
import forwards_backwards_api.{Forwards, ProgramLocation}

import scala.collection.immutable.Stack

case class DisjunctState(loc : ProgramLocation, stores : Set[AbstrStore],
                         callStack : Stack[(ProgramLocation,Iterable[Constraint])], //Each pair is a program location (to jump back to) and some (possibly-empty) set of constraints to re-add to queries when popping the stack
                         containingLoopInitialStores : Stack[(ProgramLocation,AbstrStore)]) {
  override def toString = s"$loc => ${stores.mkString("{"," v " ,"}")}"
  val block = loc.getNode.getBlock
  val function = loc.getNode.getBlock.getFunction

  def isSatisfiable(f : Forwards) : Boolean = stores exists {_.isSatisfiable(f,loc)}
}
