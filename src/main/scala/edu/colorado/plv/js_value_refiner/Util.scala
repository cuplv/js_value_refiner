package edu.colorado.plv.js_value_refiner

import dk.brics.tajs.flowgraph.jsnodes.{BinaryOperatorNode,UnaryOperatorNode}
import dk.brics.tajs.lattice.Value

/**
 * Utility methods for js_value_refiner
 */
object Util {

  def opToString(op : UnaryOperatorNode.Op) : String = op match {
    case UnaryOperatorNode.Op.COMPLEMENT => "~"
    case UnaryOperatorNode.Op.MINUS => "-"
    case UnaryOperatorNode.Op.NOT => "!"
    case UnaryOperatorNode.Op.PLUS => "+"
  }
  def opToString(op : BinaryOperatorNode.Op) : String = op match {
    case BinaryOperatorNode.Op.ADD =>        "+"
    case BinaryOperatorNode.Op.AND =>        "&"
    case BinaryOperatorNode.Op.DIV =>        "/"
    case BinaryOperatorNode.Op.EQ  =>        "=="
    case BinaryOperatorNode.Op.GE  =>        ">="
    case BinaryOperatorNode.Op.GT  =>        ">"
    case BinaryOperatorNode.Op.IN  =>        "in"
    case BinaryOperatorNode.Op.INSTANCEOF => "instanceof"
    case BinaryOperatorNode.Op.LE  =>        "<="
    case BinaryOperatorNode.Op.LT  =>        "<"
    case BinaryOperatorNode.Op.MUL =>        "*"
    case BinaryOperatorNode.Op.NE  =>        "!="
    case BinaryOperatorNode.Op.OR  =>        "|"
    case BinaryOperatorNode.Op.REM =>        "%"
    case BinaryOperatorNode.Op.SEQ =>        "==="
    case BinaryOperatorNode.Op.SHL =>        "<<"
    case BinaryOperatorNode.Op.SHR =>        ">>"
    case BinaryOperatorNode.Op.SNE =>        "!=="
    case BinaryOperatorNode.Op.SUB =>        "-"
    case BinaryOperatorNode.Op.USHR =>       ">>>"
    case BinaryOperatorNode.Op.XOR =>        "^"

  }
}