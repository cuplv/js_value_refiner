package edu.colorado.plv

import dk.brics.tajs.lattice.Value
import dk.brics.tajs.flowgraph.{Function => TAJSFunction}
import edu.colorado.plv.js_value_refiner.constraint.{Constraint, PureExpr, PureVal, PureVar}
import edu.colorado.plv.js_value_refiner.memory.{ProgramVar, Register, Variable}
import edu.colorado.plv.value_refiner.AbstractValue
import forwards_backwards_api.{Forwards, ProgramLocation}
import forwards_backwards_api.memory.{MemoryLocation, Register => TajsReg, Variable => TajsVar}

import scala.language.implicitConversions
import scala.language.postfixOps

package object js_value_refiner {

  def verbose(x : Any) : Unit = if(Options.VERBOSE) println(x)
  def debug  (x : Any) : Unit = if(Options.DEBUG  ) println(Console.YELLOW + x + Console.RESET)
  def warn   (x : Any) : Unit = if(Options.WARN   ) println(Console.RED + x + Console.RESET)

  implicit def var2memloc(v : ProgramVar) : MemoryLocation = v match {
    case Variable(name,_) => new TajsVar(name)
    case Register(num,_) => new TajsReg(num)
  }
  implicit def wrapTajsValue(v : Value) : AbstractValue = AbstractValue(v)
  implicit def sym2pure(v : SymbolicVar) : PureExpr = PureVar(v)
  implicit def val2pure(v : Value) : PureExpr = PureVal(v)
  implicit def constraints2store(cs : Iterable[Constraint]) : AbstrStore = AbstrStore(cs toSeq : _*)
  implicit def propertyIdent2pure(prop : Either[String,SymbolicVar]) : PureExpr = prop.fold({s => PureVal(Value makeStr s)},sym2pure)
  implicit def forwards2AssumptionTracking(forwards : Forwards) : AssumptionTrackingForwards = AssumptionTrackingForwards apply forwards
  implicit def location2function(loc : ProgramLocation) : TAJSFunction = loc.getNode.getBlock.getFunction

  def isEntry(f : Forwards, loc : ProgramLocation) =
    loc.getNode.getBlock.isEntry && loc.getNode.getBlock.getFunction.isMain && f.getPredecessors(loc).isEmpty

  def getScopeFn(ident : String, fn : TAJSFunction) : TAJSFunction =
    if (fn.getOuterFunction == null
       || ident == "this"
       || fn.getVariableNames.contains(ident)
       || fn.getParameterNames.contains(ident)) fn
    else getScopeFn(ident,fn.getOuterFunction)
}
package value_refiner {
  object AbstractValue {
    val top_non_obj = List(Value.makeAnyBool,Value.makeAnyNum,Value.makeAnyStr,Value.makeNull,Value.makeUndef) reduce { _ join _ }
    val bot = Value.makeNone
  }
  case class AbstractValue(v : Value) {
    def couldBeBool = !v.isNotBool
    def couldBeNum = !v.isNotNum
    def couldBeStr = !v.isNotStr
    def couldBeNull = !v.isNotNull
    def couldBeUndef = !v.isNotUndef

    def isDefinitelyBool = ! (v.isNotBool || v.isMaybeOtherThanBool)
    def isDefinitelyNum = v.restrictToNotNum equals Value.makeNone
    def isDefinitelyStr = v.restrictToNotStr equals Value.makeNone
    def isDefinitelyNull = v.restrictToNotNull equals Value.makeNone
    def isDefinitelyUndef = v.restrictToNotUndef equals Value.makeNone

  }
}
