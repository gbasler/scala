object Test {

  sealed abstract class Expr

  sealed abstract class BinOp

  case object Equiv extends BinOp

  case object Xor extends BinOp

  sealed abstract class NOp

  case object And extends NOp

  case object Or extends NOp

  final case class BinaryOp(op: BinOp, a: Expr, b: Expr) extends Expr

  final case class NaryOp(op: NOp, ops: Seq[Expr]) extends Expr

  def foo(e: Expr): Unit = e match {
    case BinaryOp(Equiv, a, b) =>
    case BinaryOp(Xor, a, b)   =>
    case NaryOp(Or, ops)       =>
    case NaryOp(And, ops)      =>
  }

}

