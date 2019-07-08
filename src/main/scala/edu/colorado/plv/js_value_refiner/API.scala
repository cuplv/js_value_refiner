package edu.colorado.plv.js_value_refiner

import java.util

import dk.brics.tajs.flowgraph.jsnodes.{CallNode, ReadPropertyNode, WritePropertyNode}
import dk.brics.tajs.lattice.{ObjectLabel, Value}
import edu.colorado.plv.js_value_refiner.constraint._
import edu.colorado.plv.js_value_refiner.memory._
import forwards_backwards_api.{memory => tajs, _}

import scala.collection.JavaConversions._
import scala.collection.immutable.Stack

sealed abstract class RefinementConstraint  extends Formula {
  def toConstraints(atLoc : ProgramLocation) : Set[Constraint]
}
case class EqConstraint  (mem : tajs.MemoryLocation, value : Value) extends RefinementConstraint {
  def toConstraints(atLoc : ProgramLocation) = mem match {
    case reg: tajs.Register => Set(LocalConstraint(Register(reg.getId,atLoc), SymbolicVar(reg.getId), None), PureConstraint.make_eq(SymbolicVar(reg.getId), value, atLoc))
    case prop: tajs.Property if prop.getName.isMaybeSingleStr && prop.getName.isDefinitelyStr =>
      val v0 = SymbolicVar(0)
      Set(
        HeapConstraint(Left(Value makeObject prop.getObject), Left(prop.getName.getStr), v0),
        PureConstraint.make_eq(v0, value, atLoc)
      )
    case prop: tajs.Property =>
      val (v0, v1, v2) = (SymbolicVar(0), SymbolicVar(1), SymbolicVar(2))
      Set(
        PureConstraint.make_eq(v2, prop.getName, atLoc),
        HeapConstraint(Left(Value makeObject prop.getObject), Right(v2), v0),
        PureConstraint.make_eq(v0, value, atLoc)
      )
    case v: tajs.Variable =>
      if (v.getScope.isPresent) {
        Set(LocalConstraint(Variable(v.getName, v.getScope.get()), SymbolicVar(0), None), PureConstraint.make_eq(SymbolicVar(0), value, atLoc))
      } else {
        Set(LocalConstraint(Variable(v.getName, atLoc), SymbolicVar(0), None), PureConstraint.make_eq(SymbolicVar(0), value, atLoc))
      }
  }
}
case class Conjunction(l : RefinementConstraint, r : RefinementConstraint) extends RefinementConstraint {
  def toConstraints(atLoc : ProgramLocation) = {
    def getLeaves : RefinementConstraint => Iterable[EqConstraint] = {case Conjunction(left,right) => getLeaves(left) ++ getLeaves(right) ; case x:EqConstraint => x::Nil ; case TrueConstraint => Nil}
    val eqConstraints = getLeaves(this)
    val registerConstraints : Set[Constraint] = eqConstraints.flatMap{
      case EqConstraint(reg : tajs.Register, value) => Seq( LocalConstraint(Register(reg.getId, atLoc), SymbolicVar(reg.getId), None), PureConstraint.make_eq(SymbolicVar(reg.getId),value, atLoc))
      case _ => Nil
    }.toSet
    val freshVars = ((0 until eqConstraints.map{case EqConstraint(reg:tajs.Register,_) => 1 ; case _ => 2}.sum map SymbolicVar).toSet -- registerConstraints.flatMap{_.variables}) grouped 2

    val propertyConstraints : Set[Constraint] = freshVars.zip(eqConstraints.filter(_.mem.isInstanceOf[tajs.Property]).toIterator).flatMap{case (vars,eqc) =>
        val v0 :: v1 :: Nil = vars.toList
        eqc.mem match {
          case prop : tajs.Property if prop.getName.isMaybeSingleStr && prop.getName.isDefinitelyStr =>
            Set(
              HeapConstraint(Left(Value makeObject prop.getObject),Left(prop.getName.getStr),v0),
              PureConstraint.make_eq(v0, eqc.value, atLoc)
            )
          case prop : tajs.Property =>
            Set(
              PureConstraint.make_eq(v1, prop.getName, atLoc),
              HeapConstraint(Left(Value makeObject prop.getObject),Right(v1),v0),
              PureConstraint.make_eq(v0,eqc.value, atLoc)
            )
        }
    }.toSet

    propertyConstraints ++ registerConstraints
  }
}
case object TrueConstraint extends RefinementConstraint {
  override def toConstraints(atLoc : ProgramLocation) = Set()
}


object API extends Refiner[RefinementConstraint] {

  override def refine(location: ProgramLocation, mem: tajs.MemoryLocation, constraint: RefinementConstraint, forwards: Forwards): RefineResult = {
    refine(location, mem, constraint, forwards, true)
  }

  private def refine(location: ProgramLocation, mem: tajs.MemoryLocation, constraint: RefinementConstraint, forwards: Forwards, originalQuery : Boolean): RefineResult = {
    // If this call is the original query from TAJS and it can be special-cased, do so.
    if(originalQuery) {
      specialCaseRefine(location,mem,constraint,forwards) match {
        case Some(result) => return result
        case None => //no-op
      }
    }

    val fresh = try {constraint.toConstraints(location).flatMap{_.variables.map{_.num}}.max + 1} catch {case e:UnsupportedOperationException => 0/*if no variables, max in try block throws an UOE */}
    val queries : Iterable[SetQueryAbstrStore]= mem match {
      case r : tajs.Register =>
        SetQueryAbstrStore(
          constraint.toConstraints(location) + LocalConstraint(Register(r.getId,location), SymbolicVar(r.getId), None),
          SymbolicVar(r.getId)
        )::Nil
      case p : tajs.Property =>
        // Helper function: Binds the syntactic property register where this refinement query was issued to a symbolic variable
        def assertPropReg : SymbolicVar => SetQueryAbstrStore => SetQueryAbstrStore = {sv => { query =>
          location.getNode match {
            case c : CallNode         => query.addConstraint(LocalConstraint(Register(c.getPropertyRegister,location), sv, None))
            case rp: ReadPropertyNode => query.addConstraint(LocalConstraint(Register(rp.getPropertyRegister,location),sv, None))
            case _ => query}}}

        // Helper function: Binds the syntactic base register where this refinement query was issued to a symbolic variable
        def assertBaseReg : SymbolicVar => SetQueryAbstrStore => SetQueryAbstrStore = {sv => { query =>
          location.getNode match {
            case c : CallNode         => query.addConstraint(LocalConstraint(Register(c.getBaseRegister,location), sv, None))
            case rp: ReadPropertyNode => query.addConstraint(LocalConstraint(Register(rp.getBaseRegister,location),sv, None))
            case _ => query}}}

        //        val propIsStatic = p.getName.isMaybeSingleStr && p.getName.isDefinitelyStr
        //If the property is limited to a finite set of strings, get that set and issue one static property query per string; otherwise, issue a dynamic property query.
        val finitePropSet : Option[Set[String]] =
          if(p.getName.isMaybeSingleStr != null)
            Some(Set(p.getName.getStr))
          else
            None


        //Switch on number of objects that could be read here;
        //   if 0, the read yields undef
        //   if 1, explicitly constrain that object
        //   else, explicitly constrain each possible object and add a prototype constraint
        // Also, check whether property is static or dynamic and issue the proper constraints
        val protoObjects: util.Set[ObjectLabel] = forwards.getPrototypeObjects(location, p.getObject, p.getName)
        protoObjects match {
          case objects if objects.isEmpty   =>
            val atf = AssumptionTrackingForwards(forwards)  ;  atf.getPrototypeObjects(location, p.getObject, p.getName)
            return new RefineResult(Set[Value](), atf.assumptions)
          case objects if finitePropSet.isDefined && objects.size == 1  =>
            finitePropSet.get map { prop =>
              SetQueryAbstrStore(
                constraint.toConstraints(location) + HeapConstraint(Left(Value makeObject objects.head), Left(prop), SymbolicVar(fresh)),
                SymbolicVar(fresh)
              )
            }
          case objects if objects.size == 1 /* fall-through implies dynamic property */ =>
            val (v0,v1) = (SymbolicVar(fresh), SymbolicVar(fresh+1))
                assertPropReg(v1)(SetQueryAbstrStore(
                  constraint.toConstraints(location) + HeapConstraint(Left(Value makeObject objects.head),Right(v1), v0) + PureConstraint.make_eq(v1,p.getName,location),
                  v0
                ))::Nil
          case objects if finitePropSet.isDefined /* fall-through implies objects.size > 1 */ =>
            val(v0,v1,v2) = (SymbolicVar(fresh),SymbolicVar(fresh+1),SymbolicVar(fresh+2))
            objects flatMap { obj => finitePropSet.get map { prop =>
              assertBaseReg(v1)(SetQueryAbstrStore(
                constraint.toConstraints(location)
                  + HeapConstraint(Left(Value makeObject obj), Left(prop), v0)
                  + ProtoConstraint(v1,Some(v2),Left(prop))
                  + PureConstraint.make_eq(v1, Value makeObject p.getObject, location)
                  + PureConstraint.make_eq(v2, Value makeObject obj,         location),
                v0
              ))
            }}
          case objects /* fall-through implies objects.size > 1 && dynamic property*/ =>
            val(v0,v1,v2,v3) = (SymbolicVar(fresh), SymbolicVar(fresh+1), SymbolicVar(fresh+2), SymbolicVar(fresh+3))
            objects map { obj =>
              assertPropReg(v3)(assertBaseReg(v1)(SetQueryAbstrStore(
                constraint.toConstraints(location)
                  + HeapConstraint(Left(Value makeObject obj), Right(v3), v0)
                  + ProtoConstraint(v1,Some(v2),Right(v3))
                  + PureConstraint.make_eq(v1, Value makeObject p.getObject, location)
                  + PureConstraint.make_eq(v2, Value makeObject obj,         location)
                  + PureConstraint.make_eq(v3, p.getName,                    location),
                v0
              )))
            }
        }
      case variable : tajs.Variable =>
        SetQueryAbstrStore(
          constraint.toConstraints(location) + LocalConstraint(Variable(variable.getName, if (variable.getScope.isPresent) variable.getScope.get() else location.getNode.getBlock.getFunction), SymbolicVar(100), None),
          SymbolicVar(100)
        )::Nil
      case other => sys.error(s"Can only refine registers and properties.  Received $other instead.")
    }

    verbose("="*80)
    verbose(s"Refining $mem from $location under constraints $constraint")
    verbose(s"Initial Queries:\n\t${queries mkString "\n\t"}")
    verbose("="*80)

    val exec = new Executor(forwards)
    val refinement = new RefineResult(
      exec.refine(queries, location),
      exec.forwards.assumptions
    )

    verbose("="*80)
    verbose(s"Assumptions: ${refinement.getAssumptions.map{_._2.size}.sum}")
    verbose(s"Refinement result: ${refinement.getResult}")
    verbose("="*80)

    refinement
  }

  override def refute(location: ProgramLocation, formula: RefinementConstraint, forwards: Forwards): RefutationResult = {
    val query = AbstrStore(formula.toConstraints(location))
    val exec = new Executor(forwards)

    new RefutationResult(
      exec.canRefute(DisjunctState(location,Set(query),Stack(),Stack())),
      exec.forwards.assumptions
    )
  }

  override def mkEqualityConstraint(mem: tajs.MemoryLocation, value: Value): RefinementConstraint = EqConstraint(mem,value)
  override def mkInequalityConstraint(mem: tajs.MemoryLocation, value: Value): RefinementConstraint = sys.error("Deprecated, since TAJS doesn't use it.")
  override def mkConjunctionConstraint(f1: RefinementConstraint, f2: RefinementConstraint): RefinementConstraint = Conjunction(f1,f2)
  override def mkTrueConstraint() : RefinementConstraint = TrueConstraint

  override def assumptionHolds(loc: ProgramLocation, assumption: Assumption, f: Forwards): Boolean = assumption match {
    case a : GetMemory =>          f.get(loc, a.memory)                                            == a.result
    case a : GetCalleeExits =>     f.getCalleeExits(loc)                                           == a.result
    case a : GetCallSites =>       f.getCallSites(loc)                                             == a.result
    case a : GetPredecessors =>    f.getPredecessors(loc)                                          == a.result
    case a : GetBinOp =>           f.binop(loc, a.v1, a.op, a.v2)                                  == a.result
    case a : GetUnOp =>            f.unop(loc, a.op, a.v)                                          == a.result
    case a : GetForInProps =>      f.getForInProperties(loc,a.obj)                                 == a.result
    case a : GetProtoObjects =>    f.getPrototypeObjects(loc,a.obj,a.prop)                         == a.result
    case a : InferPropertyNames => f.inferPropertyNames(loc,a.base,a.targetValue,a.usePrototypes)  == a.result
    case a : InferPropertyValue => f.inferPropertyValue(loc,a.base,a.propertyName,a.usePrototypes) == a.result
  }

  // When TAJS makes queries at WritePropertyNodes, we can sometimes use the structure of the node to build a more
  // concise and efficient query than the 1-1 translation from the RefinementConstraint would give us.  IF:
  // -- we are refining the value register of the property write
  // -- TAJS constrains the base register of the property write, AND
  // -- TAJS constrains the property register of the property write,
  // then we can generate a corresponding heap constraint rather than using the handful of equality constraints themselves.

  private def specialCaseRefine(location: ProgramLocation, mem: tajs.MemoryLocation, constraint: RefinementConstraint, forwards: Forwards): Option[RefineResult] = {
    val preds:Iterable[ProgramLocation] = forwards.getPredecessors(location).toIterable
      if(preds.size != 1) return None
      preds.head.getNode match {
      case w:WritePropertyNode =>
        mem match {
          case r : tajs.Register if r.getId == w.getValueRegister => //NO OP, fall through to special case logic
          case _ => return None//this query can't be special-cased
        }
        // Given a register and a refinement constraint, return the value that register is constrained to, if it is constrained
        def eqconstraintOnReg : Int => RefinementConstraint=>Option[Value] = { reg => {
          case Conjunction(l,r) => val l_res = eqconstraintOnReg(reg)(l)
            if(l_res isDefined) l_res
            else eqconstraintOnReg(reg)(r)
          case EqConstraint(m,v) if m.isInstanceOf[tajs.Register] && m.asInstanceOf[tajs.Register].getId == reg => Some(v)
          case _ => None
        }}

        // Given a register and a refinement constraint, return a new constraint that doesn't constrain the register but is otherwise unchanged from the input constraint.
        def stripConstraintsOnReg : Int => RefinementConstraint => RefinementConstraint = {reg => {
          case Conjunction(l,r) => Conjunction(stripConstraintsOnReg(reg)(l), stripConstraintsOnReg(reg)(r))
          case EqConstraint(r:tajs.Register,v) if r.getId == reg => TrueConstraint
          case x => x
        }}

        val propertyConstrained : Boolean = mem match {
          case r : tajs.Register => r.getId == w.getValueRegister
          case _ => false
        }

        val baseObj  : Option[ObjectLabel] = eqconstraintOnReg(w.getBaseRegister)(constraint) flatMap { v => //{ case v if v.isMaybeSingleObjectLabel => v.getObjectLabels.headOption ; case _ => None}
          if(v.isMaybeSingleObjectLabel) Some(v.getObjectLabels.iterator.next) else None
        }

        val propVal : Option[Value] = eqconstraintOnReg(w.getPropertyRegister)(constraint)
        baseObj flatMap {obj => propVal map {prop =>
          refine(
            location,
            new tajs.Property(obj,prop),
            stripConstraintsOnReg(w.getBaseRegister)(stripConstraintsOnReg(w.getPropertyRegister)(constraint)),
            forwards,
            false
          )
        }}
      case _ => None
    }
  }
}
