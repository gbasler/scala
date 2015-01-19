sealed abstract class Expr

sealed abstract class BinOp

case object Equiv extends BinOp

case object Xor extends BinOp

sealed abstract class NOp

case object And extends NOp

case object Or extends NOp

final case class BinaryOp(op: BinOp, a: Expr, b: Expr) extends Expr

final case class NaryOp(op: NOp, ops: Seq[Expr]) extends Expr

object Test {

  def exhausto1(expr: Expr): Unit = expr match {
    case BinaryOp(Equiv, a, b) =>
    case BinaryOp(Xor, a, b) =>
    case NaryOp(Or, ops) =>
    case NaryOp(And, ops) =>
  }

  def exhausto2(expr: Expr): Unit = expr match {
//    case BinaryOp(_, a, b) =>
//    case NaryOp(_, ops) =>
    case NaryOp(And, ops) =>
  }

    /*
      def exhausto1(expr: Expr): Unit = expr match {
    case BinaryOp(Equiv, a, b) =>
    case NaryOp(Or, ops) =>
  }

  def exhausto2(expr: Expr): Unit = expr match {
    case BinaryOp(Equiv, a, b) =>
    case BinaryOp(Xor, a, b) =>
    case NaryOp(Or, ops) =>
  }

  def exhausto3(expr: Expr): Unit = expr match {
    case BinaryOp(Equiv, a, b) =>
    case BinaryOp(Xor, a, b) =>
    case NaryOp(Or, ops) =>
    case NaryOp(And, ops) =>
  }
    */

}

