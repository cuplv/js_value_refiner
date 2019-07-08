package edu.colorado.plv.js_value_refiner

import dk.brics.tajs.flowgraph.jsnodes.{CallNode, ReturnNode}
import dk.brics.tajs.lattice.Value
import edu.colorado.plv.js_value_refiner.constraint._
import edu.colorado.plv.js_value_refiner.memory.{Register, Variable}
import forwards_backwards_api.memory.{MemoryLocation, Property}
import forwards_backwards_api.{Forwards, ProgramLocation}

import scala.language.postfixOps
import scala.collection.JavaConversions._

object SetQueryAbstrStore {
  def apply(constraints: Set[Constraint], trackedVal: PureExpr, canonicalized: Boolean = false): SetQueryAbstrStore =
    new SetQueryAbstrStore(constraints, trackedVal, canonicalized)
  def unapply(arg: SetQueryAbstrStore): Option[(Set[Constraint], PureExpr)] = Some(arg.constraints,arg.trackedValue)
}

class SetQueryAbstrStore(override val constraints : Set[Constraint],
                         val trackedValue : PureExpr,
                         override val canonicalized : Boolean = false) extends AbstrStore(constraints, canonicalized) {
  override def toString = trackedValue.toString + " ; " + super.toString

  override def equals(other : Any) : Boolean = other match {
    case o:SetQueryAbstrStore => this.constraints == o.constraints && this.trackedValue == o.trackedValue
    case _ => false
  }

  def getBaseValFromProtoConstraint(protoOpt: Option[ProtoConstraint], heap: HeapConstraint, f: Forwards, loc: ProgramLocation) : Value = {
    val base_val : Value = protoOpt match {
      case Some(proto) => {
        val base_mem_location: MemoryLocation =
          localConstraints.find(_.snk == proto.child) match {
            case Some(lc) => lc.src
            case None => heapConstraints.find(hc => hc.prop.isLeft && hc.rcvr.isLeft) match {
              case Some(hc) => new Property(hc.rcvr.left.get.getObjectLabels.head, Value.makeStr(hc.prop.left.get))
              case None => ??? //Unbound base memory location for property inference
            }
          }
        f.get(loc, base_mem_location)
      }
      case None => {
        heap.rcvr.left.get}
    }
    base_val
  }


  def getDefiniteValue(previousLoc : ProgramLocation, loc : ProgramLocation, f : Forwards) : Option[Set[Value]] = {
    if (trackedValue.variables.isEmpty)
      Some(Set(trackedValue.toAbstractVal(f)))
    else {
      if (trackedValue.variables.size == 1 &&
        !(previousLoc.getNode.isInstanceOf[CallNode] || previousLoc.getNode.isInstanceOf[ReturnNode])) {
          val trackedVariable = trackedValue.variables.iterator.next

          val optRes = localConstraints
            .filter(_.snk == trackedVariable)
            .map(_.src) match { //all program variables constraining the tracked variable
              case Nil => None
              case vs if vs.exists(pv =>
                (pv.isInstanceOf[Variable] && !pv.asInstanceOf[Variable].scope.equals(previousLoc.getNode.getBlock.getFunction)) ||
                  (pv.isInstanceOf[Register] && !pv.asInstanceOf[Register].scope.equals(previousLoc.getNode.getBlock.getFunction))
              ) => None
              case vs => Some(Value.join(vs.map(f.get(previousLoc, _))));
          }
          if (optRes.isDefined && optRes.get.typeSize() == 1 && optRes.get.getObjectLabels.size < 3 && !optRes.get.isMaybeFuzzyStr) {
            return Some(Set(optRes.get))
          }
      }

      val propertyInferenceTemplate = getPropertyInferenceTemplate(f)
      if (propertyInferenceTemplate.isDefined) {
        val (protoOpt, heap, pure) = propertyInferenceTemplate.get

        //        val symbolic_property_name = heap.prop.right.get
        val binding = getDefiniteValBinding(pure).get._2
        val base_val = getBaseValFromProtoConstraint(protoOpt, heap, f, loc)

        protoOpt match {
          case Some(proto) => debug(
            s" Candidate for property name inference derived from constraints:" +
              s"\n\t$proto\n\t$heap\n\t$pure")
          case None => debug (s" derived from constraints:\n\t$heap\n\t$pure")
        }

        val inferredPropertyNamesOpt = f.inferPropertyNames(loc, base_val, binding, true)
        if (inferredPropertyNamesOpt.isPresent) Some(inferredPropertyNamesOpt.get.toSet) else None
      } else {
        val propertyValueTemplate = getPropertyValueTemplate()
        if (propertyValueTemplate.isDefined) {
          val (proto, heap, propName) = propertyValueTemplate.get
          val base_val = getBaseValFromProtoConstraint(Some(proto), heap, f, loc)
          val inferredPropertyValueOpt = f.inferPropertyValue(loc, base_val, Value.makeStr(propName), true)
          if (inferredPropertyValueOpt.isPresent) Some(inferredPropertyValueOpt.get.toSet) else None
        } else
          None
      }
    }
  }

  def getPropertyValueTemplate() : Option[(ProtoConstraint, HeapConstraint, String)] = {
    val trackedVar : SymbolicVar = trackedValue match {
      case v : PureVar => v.v
      case _ => return None
    }

    // Try to find a proto constraint / heap constraint pair such that:
    //   (A) the heap constraint has the tracked value as the constraining value
    //   (B) the proto constraint has the same property as the above heap constraint
    //   (C) the parent of the proto constraint is the receiver of the heap constraint
    heapConstraints.foreach { heap =>
      if (heap.snk equals trackedVar) { // condition (A)
        protoConstraints.foreach { proto =>
          if (heap.prop.isLeft && (heap.prop equals proto.prop) && // condition (B)
              heap.rcvr.isRight && heap.rcvr.right.toOption.equals(proto.parent)) { // condition (C)
            return Some(proto, heap, heap.prop.left.get)
          }
        }
      }

    }
    None
  }

  def getPropertyInferenceTemplate(f : Forwards) : Option[(Option[ProtoConstraint],HeapConstraint,PureConstraint)] = {
    val trackedVar : SymbolicVar = trackedValue match {
      case v : PureVar => v.v
      case _ => return None
    }

    def isSamePropVar(prop : Either[String,SymbolicVar]) : Boolean = {
      prop.fold( _ => false, v => v equals trackedVar)
    }

    def propNameContainedInPureConstraintWithTrackedVar(propName: String): Boolean = {
      // does constraints of the form (Sx == propName) or !!(Sx == propName) exist
      return !pureConstraints
        .filter(_.variables.contains(trackedVar))
        .filter(_.lhs.negationsAndBase._1 % 2 == 0)
        .map(_.lhs.negationsAndBase._2)
        .filter(_.isInstanceOf[PureBinOp])
        .map(_.asInstanceOf[PureBinOp].r)
        .filter(_.isInstanceOf[PureVal])
        .map(_.asInstanceOf[PureVal].toAbstractVal(f, null)) // PureVal does not use knownVals
        .filter(_ == Value.makeStr(propName)).isEmpty
    }

    // Try to find proto constraint / heap constraint pair such that:
    //  (A) the proto constraint has a fixed property name and the name is bound to the tracked var in a PureConstraint
    //  (B) the heap constraint has the same fixed property as the proto constraint
    //  (C) there exists a pure constraint binding the sink of the heap constraint to an abstract Value
    protoConstraints.foreach { proto =>
      if (proto.prop.isLeft && propNameContainedInPureConstraintWithTrackedVar(proto.prop.left.get)) { // condition (A)
        heapConstraints.foreach { heap =>
          if (heap.prop.isLeft && heap.prop.left == proto.prop.left) { // condition (B)
            pureConstraints.foreach { pure =>
              if(
                getDefiniteValBinding(pure).fold(false)(binding => binding._1 == heap.snk) // condition (C)
              ) return Some((Some(proto),heap,pure))
            }
          }
        }

      }
    }


    // Try to find a proto constraint / heap constraint pair such that:
    //  (A) the proto constraint has the tracked value as its property name
    //  (B) the heap constraint has the tracked value as its property name
    //  (C) the parent of the proto constraint is the receiver of the heap constraint
    //  (D) there exists a pure constraint binding the sink of the heap constraint to an abstract Value
    protoConstraints.foreach { proto =>
      if(isSamePropVar(proto.prop)){//condition (A))
        heapConstraints.foreach { heap =>
          if(
            isSamePropVar(heap.prop) && // condition (B)
            heap.rcvr.isRight && heap.rcvr.right.toOption.equals(proto.parent) // condition (C)
          ) {
            pureConstraints.foreach { pure =>
              if(
                getDefiniteValBinding(pure).fold(false)(binding => binding._1 == heap.snk) // condition (D)
              ) return Some((Some(proto),heap,pure))
            }
          }
        }
      }
    }
    heapConstraints.foreach { heap =>
      if(isSamePropVar(heap.prop) && heap.rcvr.isLeft) { // Heap constraint, where the receiver is a Value
        pureConstraints.foreach { pure =>
          if(
            getDefiniteValBinding(pure).fold(false)(binding => binding._1 == heap.snk) // condition (D)
          ) return Some((None,heap,pure))
        }
      }
    }
    None
  }

  override def addConstraint(c : Constraint) : SetQueryAbstrStore = SetQueryAbstrStore(constraints + c, trackedValue)
  override def dropConstraints(predicate : Constraint => Boolean) : SetQueryAbstrStore = SetQueryAbstrStore(filterNot(predicate).toSet,trackedValue)
  override def dropConstraint(c : Constraint) : SetQueryAbstrStore =
    if(constraints contains c)
      SetQueryAbstrStore(constraints-c, trackedValue)
    else
      throw new IllegalArgumentException("Can't remove a constraint that's not already in the AbstractStore")

  override lazy val variables : Set[SymbolicVar] = constraints.flatMap{_.variables} union trackedValue.variables

  override def substitute(oldV : SymbolicVar, newV : SymbolicVar) : AbstrStore = {
    Executor.testTimeout()
    SetQueryAbstrStore(constraints map {_.substitute(oldV,newV)}, trackedValue.substitute(oldV,newV))
  }

  override def constrains(v : SymbolicVar) : Boolean =
    (trackedValue.variables contains v) || (filterNot {_.isInstanceOf[LocalConstraint] } exists { _.variables contains v })

  override def getFreshVar : SymbolicVar =
    (SymbolicVar(0) /: (constraints.flatMap({_.variables}) ++ trackedValue.variables)) { (lowest_fresh, variable) =>
    variable match {
      case SymbolicVar(i) if i >= lowest_fresh.num => SymbolicVar(i+1)
      case _ => lowest_fresh
    }}

  override def canonicalize(f : Forwards, loc : ProgramLocation) : SetQueryAbstrStore = {
    if(this.canonicalized) return this
    // get symbolic variable equivalence classes that arise from heap and local constraints
    val equiv_classes = getSymVarEquivClasses
    //Helper functions to update constraints
    def canon: SymbolicVar => SymbolicVar = { sv =>
      equiv_classes find {_ contains sv} match {
        case Some(equiv_class) => equiv_class.head
        case None => sv
      }}
    def canonPure: PureExpr => PureExpr = {
      case PureBinOp(l, op, r, binop_loc) =>
        val binop = PureBinOp(canonPure(l), op, canonPure(r), binop_loc)
        if(binop.variables.isEmpty) binop.toAbstractVal(f)
        else binop
      case PureUnOp(op, expr, unop_loc) =>
        val unop = PureUnOp(op, canonPure(expr), unop_loc)
        if(unop.variables.isEmpty) unop.toAbstractVal(f)
        else unop
      case p: PureVal => p
      case PureVar(v) => PureVar(canon(v))
    }
    val resultFromSuper = SetQueryAbstrStore(super.canonicalize(f,loc).constraints, canonPure(trackedValue))

    //Get all static heap constraints on native objects
    val native_heap_constraints = resultFromSuper.heapConstraints.filter{hc =>
      hc.rcvr.isLeft && // heap constraint is explicit - i.e. receiver is an abstract object, not a symbolic variable
      hc.rcvr.left.get.getObjectLabels.head.isHostObject && // That receiver is a native object (i.e. HostObject)  (call to .head is safe because of assertion in HeapConstraint.scala
      hc.prop.fold(Natives.getPropNames(hc.rcvr.left.get.getObjectLabels.head.getHostObject).contains, {_ => false}) && //heap constraint is static, and its field exists on the native object
      !(loc.getNode.isInstanceOf[CallNode] && loc.getNode.asInstanceOf[CallNode].getTajsFunctionName != null) // TAJS doesn't like calls to forwards.get at locations that call TAJS functions.
    }
    val nativeHeapsCollapsed = ((Some(resultFromSuper):Option[SetQueryAbstrStore]) /: native_heap_constraints) {case (acc,curr) => acc flatMap {st =>
      val native_fn = f.get(loc,new Property(curr.rcvr.left.get.getObjectLabels.head,Value makeStr curr.prop.left.get))
      BackwardsTransfer.writePure(st dropConstraint curr,loc,curr.snk,native_fn,f).asInstanceOf[Option[SetQueryAbstrStore]]
    }}
    assert(nativeHeapsCollapsed.isDefined) //Should always hold, since we're only collapsing heap constraints on native functions we know exist.
    val result_store = nativeHeapsCollapsed.get
    SetQueryAbstrStore(result_store.constraints, result_store.trackedValue, true)

  }
  override def meet(other : AbstrStore) : SetQueryAbstrStore = ???

  //Iterable return interpreted as disjunction
  override def join(other : AbstrStore) : Iterable[SetQueryAbstrStore] = other match {
    case other : SetQueryAbstrStore =>
      val collated = this.collateVarsWith(other).asInstanceOf[SetQueryAbstrStore]
      val intersection = collated.constraints intersect other.constraints
      val compatibleHeapConstraints = collated.heapConstraints.filter{chc =>
        other.heapConstraints.exists{ohc =>ohc.rcvr == chc.rcvr && ohc.snk == chc.snk} && ! intersection.contains(chc)
      }
      val intersection_prime = (intersection /: compatibleHeapConstraints) {(acc,curr) => acc + HeapConstraint(curr.rcvr,Right(acc.getFreshVar), curr.snk)}

//      if (collated.trackedValue == other.trackedValue)
        Some(SetQueryAbstrStore(intersection_prime, collated.trackedValue))
//      else {
//        Seq(
//          SetQueryAbstrStore(intersection_prime, collated.trackedValue),
//          SetQueryAbstrStore(intersection_prime, other.trackedValue)
//        )
//      }
    case _ : AbstrStore => throw new IllegalArgumentException("Can't take the meet of an AbstrStore and a SetQueryAbstrStore")
  }
}
