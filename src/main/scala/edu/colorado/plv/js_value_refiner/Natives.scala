package edu.colorado.plv.js_value_refiner

import dk.brics.tajs.analysis.nativeobjects.{ECMAScriptObjects, TAJSFunction}
import dk.brics.tajs.flowgraph.TAJSFunctionName
import dk.brics.tajs.flowgraph.jsnodes.CallNode
import dk.brics.tajs.flowgraph.jsnodes.BinaryOperatorNode.{Op => BinOp}
import dk.brics.tajs.lattice.{HostObject, Value}
import edu.colorado.plv.js_value_refiner.constraint._
import edu.colorado.plv.js_value_refiner.memory.Register
import forwards_backwards_api.{Forwards, ProgramLocation}

import scala.language.postfixOps
import scala.collection.JavaConversions._

/**
  * Model JavaScript Native calls
  */
object Natives {
  def getPropNames(hostObj: HostObject): Iterable[String] = {
    hostObj match {
      case ECMAScriptObjects.OBJECT => Seq("prototype", "defineProperty", "create", "defineProperties", "freeze", "getOwnPropertyDescriptor", "getOwnPropertyNames", "getPrototypeOf", "isExtensible", "isFrozen", "isSealed", "keys", "preventExtensions", "seal")
      case ECMAScriptObjects.OBJECT_PROTOTYPE => Seq("toString", "toLocaleString", "valueOf", "hasOwnProperty", "isPrototypeOf", "propertyisEnumerable")
      case ECMAScriptObjects.FUNCTION => Seq("prototype")
      case ECMAScriptObjects.FUNCTION_PROTOTYPE => Seq("toString", "apply", "call", "bind")
      case ECMAScriptObjects.ARRAY => Seq("isArray", "prototype")
      case ECMAScriptObjects.ARRAY_PROTOTYPE => Seq("toString", "toLocaleString", "concat", "join", "pop", "push", "reverse", "shift", "slice", "some", "sort", "splice", "unshift", "indexOf", "every", "filter", "map", "reduce", "reduceRight", "lastIndexOf")
      case ECMAScriptObjects.STRING => Seq("prototype", "fromCharCode")
      case ECMAScriptObjects.STRING_PROTOTYPE => Seq("toString", "valueOf", "charAt", "charCodeAt", "concat", "indexOf", "lastIndexOf", "localeCompare", "match", "replace", "search", "slice", "split", "substr", "substring", "toLowerCase", "toLocaleLowerCase", "toUpperCase", "toLocaleUpperCase", "trim")
      case ECMAScriptObjects.BOOLEAN => Seq("prototype")
      case ECMAScriptObjects.BOOLEAN_PROTOTYPE => Seq("toString", "valueOf")
      case ECMAScriptObjects.NUMBER => Seq("prototype")
      case ECMAScriptObjects.NUMBER_PROTOTYPE => Seq("toString", "toLocaleString", "valueOf", "toFixed", "toExponential", "toPrecision")
      case ECMAScriptObjects.MATH => Seq("max", "min", "pow", "random", "round", "sin", "sqrt", "tan", "abs", "acos", "asin", "atan", "atan2", "ceil", "cos", "exp", "floor", "log")
      case ECMAScriptObjects.DATE => Seq("parse", "UTC", "prototype", "now")
      case ECMAScriptObjects.DATE_PROTOTYPE => Seq("toString", "toDateString", "toTimeString", "toLocaleString", "toLocaleDateString", "toLocaleTimeString", "valueOf", "getTime", "getFullYear", "getUTCFullYear", "getMonth", "getUTCMonth", "getDate", "getUTCDate", "getDay", "getUTCDay", "getHours", "getUTCHours", "getMinutes", "getUTCMinutes", "getSeconds", "getUTCSeconds", "getMilliseconds", "getUTCMilliseconds", "getTimezoneOffset", "setTime", "setMilliseconds", "setUTCMilliseconds", "setSeconds", "setUTCSeconds", "setMinutes", "setUTCMinutes", "setHours", "setUTCHours", "setDate", "setUTCDate", "setMonth", "setUTCMonth", "setFullYear", "setUTCFullYear", "toISOString", "toJSON", "toUTCString", "getYear", "setYear", "toGMTString")
      case ECMAScriptObjects.REGEXP => Seq("prototype")
      case ECMAScriptObjects.REGEXP_PROTOTYPE => Seq("compile", "exec", "lastIndex", "test", "toString")
      case ECMAScriptObjects.ERROR => Seq("prototype", "toString")
      case ECMAScriptObjects.EVAL_ERROR => Seq("prototype")
      case ECMAScriptObjects.RANGE_ERROR => Seq("prototype")
      case ECMAScriptObjects.REFERENCE_ERROR => Seq("prototype")
      case ECMAScriptObjects.SYNTAX_ERROR => Seq("prototype")
      case ECMAScriptObjects.TYPE_ERROR => Seq("prototype")
      case ECMAScriptObjects.URI_ERROR => Seq("prototype")
      case ECMAScriptObjects.JSON => Seq("parse", "stringify")
      case _ => Seq()
    }
  }

  /* Given a valuation of SymbolicVar's to Abstract Values, return a mapping from property names to symbolic variables whose values could have that property as a result of being a native ECMAScript Object */
  def getNativeProperties(valuation: Map[SymbolicVar, Value]): Map[String, Set[SymbolicVar]] = {
    valuation.foldLeft(Map[String, Set[SymbolicVar]]().withDefault({ _ => Set[SymbolicVar]() })) { case (prop_map, value) =>
      val propNames = value._2.getObjectLabels.flatMap {obj => getPropNames(obj.getHostObject)}
      (prop_map /: propNames) { case (m, p) => m.updated(p, m(p) + value._1) }
    }
  }

  def apply(loc: ProgramLocation, stores: Set[AbstrStore], forwards: Forwards): Set[AbstrStore] = {
    assert(loc.getNode.isInstanceOf[CallNode])
    val call = loc.getNode.asInstanceOf[CallNode]

    forwards.getCalleeExits(loc).getSecond flatMap {
      case ECMAScriptObjects.ARRAY => stores flatMap { store => processArrayConstructor(call, store, forwards, loc) }
      case ECMAScriptObjects.ARRAY_PUSH => stores flatMap { store => processArrayPush(call, store, forwards, loc) }
      case ECMAScriptObjects.ARRAY_SORT => stores flatMap { store => processArraySort(call, store, forwards, loc) }
      case ECMAScriptObjects.FUNCTION_CALL => None //Function.prototype.call callees are handled in the intra-app results
      case ECMAScriptObjects.MATH_RANDOM => stores flatMap { store => processMathRandom(call, store, forwards, loc) }
      case ECMAScriptObjects.OBJECT => stores flatMap { store => processObject(call, store, forwards, loc) }
      case ECMAScriptObjects.OBJECT_DEFINEGETTER => stores flatMap {store => processObjectDefineGetter(call, store, forwards, loc)}
      case ECMAScriptObjects.OBJECT_DEFINE_PROPERTY => stores flatMap { store => processObjectDefineProp(call, store, forwards, loc) }
      case ECMAScriptObjects.OBJECT_HASOWNPROPERTY => stores flatMap { store => processObjectHasOwnProp(call, store, forwards, loc) }
      case ECMAScriptObjects.OBJECT_ISPROTOTYPEOF  => stores flatMap { store => processObjectIsPrototypeOf(call, store, forwards, loc) }
      case ECMAScriptObjects.OBJECT_TOSTRING => stores flatMap {store => processObjectToString(call, store, forwards, loc)}
      case ECMAScriptObjects.OBJECT_VALUEOF => stores flatMap { store => processObjectValueOf(call, store, forwards, loc) }
      case tajsFunction : TAJSFunction => tajsFunction.getName match {
        case TAJSFunctionName.TAJS_ASSERT => stores flatMap { store => processTajsAssert(call, store, forwards, loc) }
        case _ : TAJSFunctionName => stores // NO OP FOR ALL OTHER TAJS FUNCTIONS
      }
      case unmodelled_native => warn(s"JavaScript native $unmodelled_native is as of yet unsupported by Value refiner") ; stores
    } toSet
  }

  private def processArrayConstructor(call: CallNode, store: AbstrStore, f: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = {
    val temp_reg = Register(1234567, loc)
    val result_reg = Register(call.getResultRegister, loc)
    def setLengthProperty(length: Int): AbstrStore => Iterable[AbstrStore] = { st =>
      BackwardsTransfer.write_prop(temp_reg, result_reg, Register(-1, loc), "length", st, f, loc) flatMap { st =>
        BackwardsTransfer.const(temp_reg, Value makeNum length, st, f, loc).map {
          _ dropConstraints { case lc: LocalConstraint => lc.src == temp_reg; case _ => false }
        }}}

    //Compute the resulting abstract store, only looking at values array is initialized with and "length" field.
    //  i.e. don't do anything about functions inherited from Array.prototype
    // There are three possible semantics for Array construction, depending the arity used:
    // Array()  : Array(0)
    // Array(k) : construct a new array of length k
    // Array(v_1, ..., v_n) : construct a new array [v_1, ..., v_n] of length n
    call.getNumberOfArgs match {
      case n if n < 2 => setLengthProperty(n)(store) flatMap {st => BackwardsTransfer.new_obj(result_reg, call, st, f, loc)}
      case n =>
        (setLengthProperty(n)(store) /: (0 until n)) { (stores, argNum) =>
          stores flatMap { st => BackwardsTransfer.write_prop(Register(call.getArgRegister(argNum), loc), result_reg, Register(-1, loc), argNum.toString, st, f, loc) }
        } map {_.canonicalize(f, loc)} filter {_.isSatisfiable(f, loc)} flatMap { st =>
          BackwardsTransfer.new_obj(result_reg, call, st, f, loc)
        } map {_.canonicalize(f, loc)} filter {_.isSatisfiable(f, loc)}
    }
  }

  private def processMathRandom(call: CallNode, store: AbstrStore, f: Forwards, loc: ProgramLocation): Iterable[AbstrStore] =
    store.getSymbolicVar(Register(call.getResultRegister, loc)) match {
      case Some(resSV) => Some(store
        .addConstraint(PureConstraint(
          PureBinOp(resSV, BinOp.LE, Value makeNum 1.0, loc), Value makeBool true, true)
        ).addConstraint(PureConstraint(
        PureBinOp(resSV, BinOp.GE, Value makeNum 0.0, loc), Value makeBool true, true)
      ))
      case _ => Some(store)
    }

  private def processTajsAssert(call: CallNode, store: AbstrStore, f: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = {
    BackwardsTransfer.const(Register(call.getArgRegister(0), loc), Value makeBool true, store, f, loc)
  }

  private def processArraySort(call: CallNode, store: AbstrStore, f: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = {
    store.getLocalBinding(Register(call.getResultRegister, loc)) match {
      case Some(resLocal) =>
        val store_with_binding = store.withLocalBinding(Register(call.getBaseRegister, loc)).dropConstraint(resLocal)
        val baseSV = store_with_binding.getSymbolicVar(Register(call.getBaseRegister, loc)).get
        val affectedConstraints = store filter {
          case h: HeapConstraint if h.rcvr == Right(resLocal.snk) => true
          case p: ProtoConstraint if p.child == resLocal.snk => true
          case _ => false
        }
        val indirectlyAffectedConstraints = affectedConstraints
          .filter {
            _.isInstanceOf[ProtoConstraint]
          }
          .map { case pc: ProtoConstraint => pc -> store.heapConstraints.filter { hc => pc.parent == Some(hc.rcvr) && pc.prop == hc.prop } }.toMap
        // For each affected heap or proto constraint, there are two cases:
        // Case 1: The property is a UInt
        //  - In this case, we drop all info about it other than the fact it's a UInt, since it will potentially have been moved around by sort()
        // Case 2: The property is _not_ a UInt
        //  - In this case, we just change the base of the constraint to the base of the call, since sort() won't have moved it.
        ((Seq(store_with_binding): Iterable[AbstrStore]) /: affectedConstraints) {
          case (stores, c: HeapConstraint) =>
            stores flatMap { st =>
              val case1: AbstrStore = st.dropConstraint(c)
                .addConstraint(HeapConstraint(Right(baseSV), Right(st.getFreshVar), c.snk))
                .addConstraint(PureConstraint.make_eq(st.getFreshVar, Value.makeAnyStrUInt, loc))
              val case2: AbstrStore = st.dropConstraint(c)
                .addConstraint(HeapConstraint(Right(baseSV), c.prop, c.snk))
                .addConstraint(PureConstraint.make_eq(c.prop.fold(Value.makeStr, PureVar), Value.makeAnyStrNotUInt, loc))
              Seq(case1, case2)
            }
          case (stores, c: ProtoConstraint) =>
            stores flatMap { st =>
              def substitute: SymbolicVar => SymbolicVar = {
                case resLocal.snk => baseSV;
                case x => x
              }
              val case1: AbstrStore =
                st.dropConstraint(c).dropConstraints(indirectlyAffectedConstraints(c).contains)
                  .addConstraint(ProtoConstraint(substitute(c.child),
                    c.parent map substitute,
                    Right(st.getFreshVar),
                    c.upperBounds map substitute,
                    c.knownProtos map { case (x, y) => (substitute(x), substitute(y)) },
                    c.varsWithProp map substitute))
                  .addConstraint(PureConstraint.make_eq(st.getFreshVar, Value.makeAnyStrUInt, loc))
                  .addConstraints(indirectlyAffectedConstraints(c) map { case HeapConstraint(rcvr, prop, snk) => HeapConstraint(rcvr, Right(st.getFreshVar), snk) })
              val case2: AbstrStore =
                st.dropConstraint(c)
                  .addConstraint(ProtoConstraint(substitute(c.child),
                    c.parent map substitute,
                    c.prop,
                    c.upperBounds map substitute,
                    c.knownProtos map { case (x, y) => (substitute(x), substitute(y)) },
                    c.varsWithProp map substitute))
                  .addConstraint(PureConstraint.make_eq(c.prop.fold(Value.makeStr, PureVar), Value.makeAnyStrNotUInt, loc))
              Seq(case1, case2)
            }
        }
      case _ => Some(store)
    }
  }

  private def processObject(call: CallNode, store: AbstrStore, f: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = {
    store.getLocalBinding(Register(call.getResultRegister, loc)) match {
      case Some(local) if call.getNumberOfArgs == 0 => BackwardsTransfer.new_obj(Register(call.getResultRegister, loc), call, store, f, loc)
      case Some(local) if call.getNumberOfArgs == 1 => Some(store addConstraint LocalConstraint(Register(call.getArgRegister(0), loc), local.snk, None))
      case Some(local) => sys.error("Wrong number of arguments to ECMAScriptObjects.OBJECT call")
      case None => Some(store) // the result of the call to Object() is unconstrained; store remains unchanged
    }
  }

  private def processArrayPush(call: CallNode, store: AbstrStore, f: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = {
    val temp_reg = Register(1234567, loc)
    val argRegs = (0 until call.getNumberOfArgs) map { i => Register(call.getArgRegister(i), loc) }
    assert(call.getNumberOfArgs == 1) //TODO(benno) handle general case?  potentially just by recursion on this handler
    val store_with_bindings =
      (store.withLocalBinding(Register(call.getBaseRegister, loc))
        /: argRegs) { (s, reg) => s.withLocalBinding(reg) }
    val baseSV = store_with_bindings.getSymbolicVar(Register(call.getBaseRegister, loc)).get

    val arr_length_heap_constraint = HeapConstraint(Right(baseSV), Left("length"), store_with_bindings.getFreshVar)
    val arr_length_SV = arr_length_heap_constraint.snk
    //TODO(benno) compute new array length?
    val res = BackwardsTransfer.write_prop(argRegs.head, Register(call.getBaseRegister, loc), temp_reg, null, store_with_bindings addConstraint arr_length_heap_constraint, f, loc) map {s =>
      s.getLocalBinding(temp_reg) match {
        case Some(local) => s dropConstraint local substitute(local.snk, arr_length_SV)//addConstraint PureConstraint.make_eq(arr_length_SV, local.snk, loc)
        case _ => s
      }
    } filter {_.isSatisfiable(f,loc)}
    res
  }

  private def processObjectDefineProp(call: CallNode, store: AbstrStore, f: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = {
    val temp_reg = Register(1234567, loc)
    val (objReg, propReg, descReg) = (Register(call getArgRegister 0, loc), Register(call getArgRegister 1, loc), Register(call getArgRegister 2, loc))

    // propStr nonNull only when the value in propReg is a single string
    val propStr : String = f.get(loc, propReg).getStr
    BackwardsTransfer.write_prop(temp_reg, objReg, propReg, propStr, store, f, loc)
      .filter {_.isSatisfiable(f,loc)}
      .flatMap { st =>
        BackwardsTransfer.read_prop(temp_reg, descReg, null, "value", st, f, loc)
      }
  }

  private def processObjectValueOf(call: CallNode, store: AbstrStore, f: Forwards, loc: ProgramLocation): Iterable[AbstrStore] = {
    val (resultReg, argReg) = (Register(call getResultRegister, loc), Register(call getBaseRegister, loc))
    store.getLocalBinding(resultReg) match {
      case Some(local) if store constrains local.snk => Some(
        store dropConstraint local addConstraint LocalConstraint(argReg, local.snk, None)
      )
      case _ => Some(store)
    }
  }

  private def processObjectHasOwnProp(call : CallNode, store : AbstrStore, f : Forwards, loc : ProgramLocation) : Iterable[AbstrStore] = {
    val (resultReg, objReg, propReg) = (Register(call getResultRegister, loc), Register(call getBaseRegister, loc), Register( call getPropertyRegister,loc))
    store.getLocalBinding(resultReg) match {
      case Some(local) if store constrains local.snk =>
        val swb = store withLocalBinding objReg withLocalBinding propReg
        val (objSV,propSV) = (swb.getSymbolicVar(objReg).get, swb.getSymbolicVar(propReg).get)

        BackwardsTransfer.const(resultReg, Value makeBool true, swb addConstraint ProtoConstraint(objSV,Some(objSV),Right(propSV)), f, loc) ++ // HAS OWN PROP
          BackwardsTransfer.const(resultReg, Value makeBool false, swb addConstraint ProtoConstraint(objSV,None,Right(propSV)), f, loc) ++ // DOES _NOT_ HAVE PROP (EVEN IN PROTO CHAIN)
          BackwardsTransfer.const(resultReg, Value makeBool false, swb addConstraint ProtoConstraint(objSV,Some(swb.getFreshVar), Right(propSV)) addConstraint PureConstraint.make_diseq(objSV, swb.getFreshVar,loc), f, loc ) //DOES _NOT_ HAVE PROP BUT A PROTO DOES
      case _ => Some(store)
    }
  }

  private def processObjectIsPrototypeOf(call : CallNode, store : AbstrStore, f : Forwards, loc : ProgramLocation) : Iterable[AbstrStore] = {
    if(call.getNumberOfArgs == 0) return BackwardsTransfer.const(Register(call.getResultRegister,loc),Value makeBool false,store,f,loc)
    val (resultReg, childReg, parentReg) = (Register(call.getResultRegister, loc), Register(call getBaseRegister, loc), Register(call getArgRegister(0), loc))
    store getLocalBinding resultReg  match {
      case Some(local) if store constrains local.snk =>
        val swb = store withLocalBinding childReg withLocalBinding parentReg
        val (childSV, parentSV) = (swb.getSymbolicVar(childReg).get, swb.getSymbolicVar(parentReg).get)
        BackwardsTransfer.const(resultReg, Value makeBool true,  swb addConstraint ProtoConstraint(childSV,Some(parentSV),Right(swb.getFreshVar),Set(),Map(),Set(parentSV)), f, loc) ++ // IS PROTOTYPE
        BackwardsTransfer.const(resultReg, Value makeBool false, swb addConstraint ProtoConstraint(childSV,None,Right(swb.getFreshVar),Set(),Map(),Set(parentSV)), f, loc) // IS NOT PROTOTYPE
      case None => Some(store)
    }
  }

  private def processObjectToString(call : CallNode, store : AbstrStore, f : Forwards, loc : ProgramLocation) : Iterable[AbstrStore] = {
    val temp_reg = Register(1234567, loc)
    BackwardsTransfer.binop(Register(call.getResultRegister,loc),Register(call.getBaseRegister,loc),BinOp.ADD, temp_reg, store, f, loc)
      .flatMap {st => BackwardsTransfer.const(temp_reg,Value makeStr "", st, f, loc)}
  }

  private def processObjectDefineGetter(call : CallNode, store : AbstrStore, f : Forwards, loc : ProgramLocation) : Iterable[AbstrStore] = {
    if(call.getNumberOfArgs < 2) None
    else throw new UnsupportedOperationException("Object.prototype.__defineGetter__ not supported by Value refiner")
  }
}
