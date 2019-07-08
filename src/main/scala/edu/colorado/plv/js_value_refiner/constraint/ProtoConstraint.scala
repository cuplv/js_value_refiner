package edu.colorado.plv.js_value_refiner.constraint

import edu.colorado.plv.js_value_refiner.SymbolicVar

/**
 * Value refiner prototype constraint of the form "proto(child,prop,upperBounds) = parent".
 * Read as "the prototype of _child_ with respect to _prop_ is _parent_, bounded by _upperBounds_"
 *
 * @param child [[SymbolicVar]] whose prototype is being constrained
 * @param parent [[Some]][ [[SymbolicVar]] ] constrained to be result of prototype lookup, or None, constraining the prototype lookup to fail
 * @param prop Property name parameterizing the prototype lookup
 * @param upperBounds [[SymbolicVar]]s that can't appear in a prototype chain witnessing this constraint
 */
case class ProtoConstraint(child : SymbolicVar,
                           parent : Option[SymbolicVar],
                           prop : Either[String,SymbolicVar],
                           upperBounds : Set[SymbolicVar] = Set(),
                           knownProtos : Map[SymbolicVar,SymbolicVar] = Map(),
                           varsWithProp : Set[SymbolicVar] = Set()) extends Constraint {
  override def variables = (upperBounds + child) ++ parent ++ prop.fold({_ => None}, {Some(_)})
  override def toString = s"proto($child,${prop.fold({x=>x},{_.toString})},${upperBounds.mkString("{",",","}")}) = ${parent.fold("None")({_.toString})} ; $knownProtos ; $varsWithProp"
  override def substitute(oldV : SymbolicVar, newV : SymbolicVar) : Constraint = {
    def sub : SymbolicVar => SymbolicVar = { sv => if(sv == oldV) newV else sv}
    ProtoConstraint(sub(child),
                    parent map sub,
                    prop.fold({str => Left(str)}, {sv => Right(sub(sv))}),
                    upperBounds map sub,
                    knownProtos map {case (k,v) => (sub(k), sub(v))},
                    varsWithProp map sub)
  }
  /** Generate new prototype constraint: this, updated with new information child.__proto__ == parent */
  def addProtoRelationship(fromVar : SymbolicVar, toVar : SymbolicVar) : ProtoConstraint =
    if(knownProtos contains fromVar) this else ProtoConstraint(child, parent, prop, upperBounds, knownProtos + (fromVar -> toVar), varsWithProp)

  /** Generate new prototype constraint: this, updated with new upper bound */
  def addUpperBound(bound : SymbolicVar) : ProtoConstraint =
    ProtoConstraint(child, parent, prop, upperBounds + bound, knownProtos, varsWithProp + bound)

  /** Generate new prototype constraint: this, updated with new information variable.hasOwnProp(prop) */
  def addVarWithProp(variable : SymbolicVar) : ProtoConstraint = ProtoConstraint(child, parent, prop, upperBounds, knownProtos, varsWithProp + variable)

  /** @return true iff there exists a path from child to ancestor in the knownProtos DAG */
  def protoPathExists(child : SymbolicVar, ancestor : SymbolicVar) : Boolean =
    (child == ancestor && varsWithProp.contains(ancestor)) || ((knownProtos contains child) && protoPathExists(knownProtos(child), ancestor))

  /** constraint is satisfiable under currently known prototype graph information
    * i.e. no upper bound is violated.
    * */
  val satisfiable : Boolean =
    parent match {
      case Some(parent) => upperBounds forall { ub => (ub != parent) &&  (ub != child) && !(protoPathExists(child, ub) && protoPathExists(ub, parent)) }
      case None =>         varsWithProp forall {! protoPathExists(child,_)}
    }


}
