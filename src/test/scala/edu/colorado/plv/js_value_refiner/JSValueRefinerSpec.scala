package edu.colorado.plv.js_value_refiner

import dk.brics.tajs.lattice.Value
import edu.colorado.plv.value_refiner.AbstractValue
import org.scalatest._

class JSValueRefinerSpec extends FlatSpec {

  def shouldRefuteFinalState(src : String, logging : Boolean = false) =
    try {
      withClue(src) {assertResult(true) {Executor.canRefuteFinalState(src,logging)}}
    } finally dk.brics.tajs.Main.reset()
  def shouldWitnessFinalState(src : String, logging : Boolean = false) =
    try {
      withClue(src) {assertResult(false) {Executor.canRefuteFinalState(src,logging)}}
    } finally dk.brics.tajs.Main.reset()


  //REFUTATION TESTS

  "js_value_refiner with boolean queries" should "handle arithmetic" in {
    shouldRefuteFinalState("test_cases/arithmetic_test_refute.js")
    shouldWitnessFinalState("test_cases/arithmetic_test_witness.js")
  }

  it should "refute properly w.r.t. forin loops" in {
    shouldWitnessFinalState("test_cases/forin_test_witness3.js")
    shouldRefuteFinalState("test_cases/forin_test_refute2.js")
    shouldRefuteFinalState("test_cases/forin_test_refute3.js")
  }

  it should "handle basic heap read/writes" in {
    shouldRefuteFinalState("test_cases/heap_test_refute.js")
    shouldRefuteFinalState("test_cases/heap_test2_refute.js")
    shouldWitnessFinalState("test_cases/heap_test_witness.js")
  }

  it should "handle aliasing" in {
    shouldRefuteFinalState("test_cases/alias_test_refute.js")
    shouldWitnessFinalState("test_cases/alias_test_witness.js")
  }

  it should "be control sensitive" in {
    shouldRefuteFinalState("test_cases/control_test_refute.js")
    shouldWitnessFinalState("test_cases/control_test_witness.js")
    shouldWitnessFinalState("test_cases/trivial_control_test_witness.js")
  }

  it should "be path sensitive" in {
    shouldRefuteFinalState("test_cases/path_sensitivity_refute.js")
    shouldWitnessFinalState("test_cases/path_sensitivity_witness.js")
  }

  it should "handle procedure calls" in {
    shouldRefuteFinalState("test_cases/interproc_test_refute.js")
    shouldWitnessFinalState("test_cases/interproc_test_witness.js")
  }

  it should "properly model constructs, invokes, and dispatches" in {
    shouldRefuteFinalState("test_cases/invoke_test_refute.js")
    shouldWitnessFinalState("test_cases/invoke_test_witness.js")
    shouldRefuteFinalState("test_cases/dispatch_test_refute.js")
    shouldWitnessFinalState("test_cases/dispatch_test_witness.js")
    shouldRefuteFinalState("test_cases/constructor_test_refute.js")
    shouldWitnessFinalState("test_cases/constructor_test_witness.js")
  }

  it should "handle prototyping" in {
    shouldRefuteFinalState("test_cases/prototype_test_refute.js")
    shouldWitnessFinalState("test_cases/prototype_test_witness.js")
  }

  it should "model the '__proto__' internal prototype field" in {
    shouldRefuteFinalState("test_cases/__proto__test_refute.js")
    shouldWitnessFinalState("test_cases/__proto__test_witness.js")
  }

  it should "be context-sensitive w.r.t. for-in loops" in {
    shouldWitnessFinalState("test_cases/forin_test_witness.js")
    shouldRefuteFinalState("test_cases/forin_test_refute.js")
    shouldWitnessFinalState("test_cases/2var_forin_test_witness.js")
    shouldRefuteFinalState("test_cases/2var_forin_test_refute.js")
  }

  it should "handle general dynamic property access" in {
    shouldRefuteFinalState("test_cases/dynamic_read_test_refute.js")
    shouldRefuteFinalState("test_cases/dynamic_read_test_refute2.js")
    shouldWitnessFinalState("test_cases/dynamic_read_test_witness.js")
  }

  it should "handle array accesses" in {
    shouldWitnessFinalState("test_cases/array_test_witness.js")
    shouldWitnessFinalState("test_cases/array_test_witness2.js")
    shouldRefuteFinalState("test_cases/array_test_refute.js")
    shouldRefuteFinalState("test_cases/array_test_refute2.js")
  }

  it should "be over-approximate w.r.t. for loops" in {
    shouldWitnessFinalState("test_cases/loop_test_witness.js")
    shouldRefuteFinalState("test_cases/loop_test_refute.js")
    shouldWitnessFinalState("test_cases/nested_loop_test_witness.js")
    shouldRefuteFinalState("test_cases/nested_loop_test_refute.js")
  }

  it should "continue from loop head when there is a refutation in the loop body" in {
    shouldWitnessFinalState("test_cases/loop_ref_test_witness.js")
    shouldRefuteFinalState("test_cases/loop_ref_test_refute.js")
  }
  it should "be able to start a query in a (possibly nested) loop body" in {
    try { withClue("witnessing loop_body_query.js") { assertResult(false) {
      Executor.canRefuteFromLine(3, "test_cases/loop_body_query.js",EqConstraint(new forwards_backwards_api.memory.Variable("prop"),Value makeStr "foo"))
    }}} finally dk.brics.tajs.Main.reset()
    try { withClue("refuting loop_body_query.js") { assertResult(true) {
      Executor.canRefuteFromLine(3, "test_cases/loop_body_query.js", EqConstraint(new forwards_backwards_api.memory.Variable("prop"), Value makeStr "baz"))
    }}} finally dk.brics.tajs.Main.reset()
    try { withClue("witnessing nested_loop_body_query.js") { assertResult(false) {
      Executor.canRefuteFromLine(5, "test_cases/nested_loop_body_query.js", EqConstraint(new forwards_backwards_api.memory.Variable("x"), Value makeStr "foobaz"))
    }}} finally dk.brics.tajs.Main.reset()
    try { withClue("refuting nested_loop_body_query.js") { assertResult(true) {
      Executor.canRefuteFromLine(5, "test_cases/nested_loop_body_query.js", EqConstraint(new forwards_backwards_api.memory.Variable("x"), Value makeStr "foobar"))
    }}} finally dk.brics.tajs.Main.reset()
  }

  it should "model native Array.prototype.sort properly" in {
    shouldWitnessFinalState("test_cases/sort_test_witness.js")
    shouldRefuteFinalState("test_cases/sort_test_refute.js")
  }

  it should "model native Object.defineProperty properly" in {
    shouldWitnessFinalState("test_cases/defineProperty_test_witness.js")
    shouldRefuteFinalState("test_cases/defineProperty_test_refute.js")
  }

  it should "handle function scoping properly" in {
    shouldWitnessFinalState("test_cases/scope_test_witness.js")
  }

  it should "respect closure semantics" in {
    shouldWitnessFinalState("test_cases/closure_test_witness.js")
    shouldRefuteFinalState("test_cases/closure_test_refute.js")
  }

  it should "respect closure semantics and path sensitivity" in {
    shouldWitnessFinalState("test_cases/path_sensitive_closures_witness.js")
    shouldRefuteFinalState("test_cases/path_sensitive_closures_refute.js")
  }


  // REFINEMENT TESTS

  def refinesToValue(variable : Either[String,Int])(v : Value,exclusive : Boolean = true)(src : String, logging : Boolean = false) = {
    try {
      Options.STOPPING_CRITERION = Options.DefiniteValueFound
      if (exclusive)
        assert(Executor.refineVarFromFinalState(variable, src, logging) == Set(v), src)
      else
        assert((AbstractValue.bot /: Executor.refineVarFromFinalState(variable, src, logging)) {_ join _} isMaybe v, src)
    } finally dk.brics.tajs.Main.reset()
  }

  "js_value_refiner with set queries" should "handle arithmetic" in {
    refinesToValue (Left("x")) (Value makeNum 100) ("test_cases/arithmetic_test_witness.js")
  }
  it should "handle basic heap read/writes" in {
    refinesToValue (Right(14)) (Value makeNum 60) ("test_cases/heap_test_witness.js")
  }

  it should "handle aliasing" in {
    refinesToValue (Right(15)) (Value makeBool true) ("test_cases/alias_test_witness.js")
  }

  it should "be control sensitive" in {
    refinesToValue (Left("x")) (Value makeBool false) ("test_cases/control_test_witness.js")
    refinesToValue (Left("x")) (Value makeBool false) ("test_cases/trivial_control_test_witness.js")
  }

  it should "be path sensitive" in {
    refinesToValue (Left("sum")) (Value makeNum 0) ("test_cases/path_sensitivity_witness.js")
    refinesToValue (Right(39)) (Value makeNum 5) ("test_cases/path_sensitivity_witness2.js")
  }

  it should "handle procedure calls" in {
    refinesToValue (Right(8)) (Value makeNum 1) ("test_cases/interproc_test_witness.js")
  }

  it should "properly model constructs, invokes, and dispatches" in {
    refinesToValue (Right(12)) (Value makeNum 5) ("test_cases/invoke_test_witness.js")
    refinesToValue (Left("x")) (Value makeNum 5) ("test_cases/dispatch_test_witness.js")
    refinesToValue (Right(9)) (Value makeNum 5) ("test_cases/constructor_test_witness.js")
  }

  it should "handle prototyping" in {
    refinesToValue (Right(12)) (Value makeNum 5) ("test_cases/prototype_test_witness.js")
  }

  it should "model the '__proto__' internal prototype field" in {
    refinesToValue (Right(12)) (Value makeNum 5) ("test_cases/__proto__test_witness.js")
  }

  it should "be context-sensitive w.r.t. for-in loops" in {
    refinesToValue (Right(18)) (Value makeNum 1) ("test_cases/forin_test_witness.js")
    refinesToValue (Right(22)) (Value makeNum 2) ("test_cases/2var_forin_test_witness.js")
  }

  it should "handle general dynamic property access" in {
    refinesToValue (Right(6)) (Value makeNum 0) ("test_cases/dynamic_read_test_witness.js")
  }

  it should "handle array accesses" in {
    refinesToValue (Right(12)) (Value makeStr "foobar") ("test_cases/array_test_witness.js")
    refinesToValue (Right(9)) (Value makeStr "foobar") ("test_cases/array_test_witness2.js")
  }

  it should "be over-approximate w.r.t. for loops" in {
    refinesToValue(Right(12))(Value makeBool true, exclusive = false)("test_cases/loop_test_witness.js")
    refinesToValue(Right(19))(Value makeBool true, exclusive = false)("test_cases/nested_loop_test_witness.js")
  }

  it should "continue from loop head when there is a refutation in the loop body" in {
    refinesToValue (Right(5))  (Value makeBool true) ("test_cases/loop_ref_test_witness.js")
  }

  it should "respect closure semantics" in {
    refinesToValue (Right(15)) (Value makeBool true) ("test_cases/closure_test_witness.js")
    refinesToValue (Right(18)) (Value makeNum 0.0) ("test_cases/path_sensitive_closures_witness.js")
  }

  it should "behave correctly for each stopping criterion" in {
    Options.STOPPING_CRITERION = Options.DefiniteValueFound
    //Should refute from end of j
    assert(! Executor.refineVarFromLine(Left("x"),"test_cases/stopping_criteria_test.js",38).contains(Value makeNum 5)); dk.brics.tajs.Main.reset()
    //Should not refute from end of f
    assert(Executor.refineVarFromLine(Left("x"),"test_cases/stopping_criteria_test.js",17).contains(Value makeNum 5)); dk.brics.tajs.Main.reset()
    //Should not refute from end of h
    assert(Executor.refineVarFromLine(Left("x"),"test_cases/stopping_criteria_test.js",27).contains(Value makeNum 5)); dk.brics.tajs.Main.reset()
    //Should not refute from end of i
    assert(Executor.refineVarFromLine(Left("x"),"test_cases/stopping_criteria_test.js",31).contains(Value makeNum 5)); dk.brics.tajs.Main.reset()

    Options.STOPPING_CRITERION = Options.FunctionEntrypoint
    //Should refute from end of j
    assert(! Executor.refineVarFromLine(Left("x"),"test_cases/stopping_criteria_test.js",38).contains(Value makeNum 5)); dk.brics.tajs.Main.reset()
    //Should refute from end of f
    assert(! Executor.refineVarFromLine(Left("x"),"test_cases/stopping_criteria_test.js",17).contains(Value makeNum 5)); dk.brics.tajs.Main.reset()
    //Should not refute from end of h
    assert(Executor.refineVarFromLine(Left("x"),"test_cases/stopping_criteria_test.js",27).contains(Value makeNum 5)); dk.brics.tajs.Main.reset()
    //Should not refute from end of i
    assert(Executor.refineVarFromLine(Left("x"),"test_cases/stopping_criteria_test.js",31).contains(Value makeNum 5)); dk.brics.tajs.Main.reset()

    Options.STOPPING_CRITERION = Options.ProgramEntrypoint
    //Should refute from end of j
    assert(! Executor.refineVarFromLine(Left("x"),"test_cases/stopping_criteria_test.js",38).contains(Value makeNum 5)); dk.brics.tajs.Main.reset()
    //Should refute from end of f
    assert(! Executor.refineVarFromLine(Left("x"),"test_cases/stopping_criteria_test.js",17).contains(Value makeNum 5)); dk.brics.tajs.Main.reset()
    //Should refute from end of h
    assert(! Executor.refineVarFromLine(Left("x"),"test_cases/stopping_criteria_test.js",27).contains(Value makeNum 5)); dk.brics.tajs.Main.reset()
    //Should not refute from end of i
    assert(Executor.refineVarFromLine(Left("x"),"test_cases/stopping_criteria_test.js",31).contains(Value makeNum 5)); dk.brics.tajs.Main.reset()
  }
}
