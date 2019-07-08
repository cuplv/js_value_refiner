package edu.colorado.plv.js_value_refiner

/**
 * Settings for backwards analysis
 */
object Options {

  /** Print debug output?
    * This debugging information is extremely granular and will be overwhelming for any significant program.
    * */
  var DEBUG : Boolean = false

  /** Print higher-level debugging output about the size of the value refiners worklist at each program location. */
  var VERBOSE : Boolean = false

  /** Print warnings? */
  var WARN : Boolean = false

  /** Per-query timeout, in milliseconds */
  val TIMEOUT = 2000

  sealed abstract class StoppingCriterion
  case object DefiniteValueFound extends StoppingCriterion // Refinement analysis stops on each path as soon as a definite value is found for the tracked expression
  case object FunctionEntrypoint extends StoppingCriterion // Refinement analysis stops when a value is found and it has reached the entrypoint of the function in which the query was issued
  case object ProgramEntrypoint extends StoppingCriterion  // Refinement analysis stops when a value is found and it has reached the program entrypoint

  var STOPPING_CRITERION : StoppingCriterion = DefiniteValueFound

}
