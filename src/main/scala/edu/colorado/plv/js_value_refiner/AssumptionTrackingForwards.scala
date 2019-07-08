package edu.colorado.plv.js_value_refiner

import java.util
import java.util.Optional

import dk.brics.tajs.flowgraph.jsnodes.BinaryOperatorNode.{Op => BinOp}
import dk.brics.tajs.flowgraph.jsnodes.UnaryOperatorNode.{Op => UnOp}
import dk.brics.tajs.lattice.{HostObject, ObjectLabel, Value}
import dk.brics.tajs.util.{Pair => tajsPair}
import forwards_backwards_api.memory.MemoryLocation
import forwards_backwards_api.{Assumption, Forwards, ProgramLocation, Properties}

import scala.collection.mutable.{Map => MMap}

case class GetMemory(memory : MemoryLocation, result : Value) extends Assumption
case class GetCalleeExits(result : tajsPair[util.Set[ProgramLocation],util.Set[HostObject]]) extends Assumption
case class GetCallSites(result : util.Set[ProgramLocation]) extends Assumption
case class GetPredecessors(result : util.Set[ProgramLocation]) extends Assumption
case class GetBinOp(v1 : Value, op: BinOp, v2 : Value, result : Value) extends Assumption
case class GetUnOp(op : UnOp, v : Value, result : Value) extends Assumption
case class GetForInProps(obj : ObjectLabel, result : Properties) extends Assumption
case class GetProtoObjects(obj : ObjectLabel, prop : Value, result : util.Set[ObjectLabel]) extends Assumption
case class InferPropertyNames(base : Value, targetValue : Value, usePrototypes : Boolean, result : Optional[util.Set[Value]]) extends Assumption
case class InferPropertyValue(base : Value, propertyName : Value, usePrototypes : Boolean, result : Optional[util.Set[Value]]) extends Assumption

object AssumptionTrackingForwards {
  def apply(forwards : Forwards, assumptions : MMap[ProgramLocation,util.Set[Assumption]] = MMap().withDefault({_ => new util.HashSet[Assumption]()})) = new AssumptionTrackingForwards(forwards,assumptions)
}


class AssumptionTrackingForwards(val forwards : Forwards, val assumptions : MMap[ProgramLocation,util.Set[Assumption]]) extends Forwards {

  private def addAssumption(a: Assumption, loc: ProgramLocation) : Unit = {
    val as = assumptions(loc)
    as add a
    assumptions += (loc -> as)
  }


  override def unop(loc: ProgramLocation, op: UnOp, v: Value): Value = forwards.unop(loc,op,v)
  override def binop(loc: ProgramLocation, v1: Value, op: BinOp, v2: Value): Value = forwards.binop(loc,v1,op,v2)

  override def getCallSites(loc: ProgramLocation): util.Set[ProgramLocation] = {
    val res = forwards.getCallSites(loc)
    addAssumption(GetCallSites(res),loc)
    res
  }

  override def getPredecessors(loc: ProgramLocation, loopUnrollingInsensitive: Boolean = true): util.Set[ProgramLocation] = {
    val res = forwards.getPredecessors(loc, loopUnrollingInsensitive)
    addAssumption(GetPredecessors(res),loc)
    res
  }

  override def get(loc: ProgramLocation, mem: MemoryLocation): Value = {
    val res = forwards.get(loc,mem)
    addAssumption(GetMemory(mem,res),loc)
    res
  }

  override def getCalleeExits(loc: ProgramLocation): tajsPair[util.Set[ProgramLocation], util.Set[HostObject]] = {
    val res = forwards.getCalleeExits(loc)
    addAssumption(GetCalleeExits(res),loc)
    res
  }

  override def getForInProperties(loc: ProgramLocation, obj: ObjectLabel): Properties = {
    val res = forwards.getForInProperties(loc, obj)
    addAssumption(GetForInProps(obj,res),loc)
    res
  }

  override def getPrototypeObjects(loc: ProgramLocation, obj: ObjectLabel, prop: Value): util.Set[ObjectLabel] = {
    val res = forwards.getPrototypeObjects(loc,obj,prop)
    addAssumption(GetProtoObjects(obj,prop,res),loc)
    res
  }

  override def inferPropertyNames(loc: ProgramLocation, base: Value, value: Value, usePrototypes: Boolean) = {
    val res = forwards.inferPropertyNames(loc,base,value, usePrototypes)
    if (res isPresent)
      addAssumption(InferPropertyNames(base, value, usePrototypes, res),loc)
    res
  }

  override def inferPropertyValue(loc: ProgramLocation, base: Value, propertyName: Value, usePrototypes: Boolean) = {
    val res = forwards.inferPropertyValue(loc,base,propertyName, usePrototypes)
    if (res isPresent)
      addAssumption(InferPropertyValue(base, propertyName, usePrototypes, res),loc)
    res
  }
}
