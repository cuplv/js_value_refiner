package edu.colorado.plv.js_value_refiner.memory

import dk.brics.tajs.flowgraph.{Function => TAJSFunction}

trait ProgramVar{
}
case class Register(num : Int, scope: TAJSFunction) extends ProgramVar {
  override def toString = s"v$num"//@[$scope#${scope.getSourceLocation.getLineNumber}]"
}

case class Variable(name : String, scope : TAJSFunction) extends ProgramVar {
  override def toString = s"$name"//@[$scope#${scope.getSourceLocation.getLineNumber}]"
}


