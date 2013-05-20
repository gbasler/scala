package scala.tools.nsc.transform.patmat

/**
 * A pair of a variable number and a sign, encoded as follows:
 *
 * @param sign 'false' means positive
 *             'true' means negative
 */
case class Lit(v: Int, sign: Boolean) {
  override def toString = s"${
    if (sign) "-" else "+"
  }$v"

  override def equals(o: Any) = o match {
    case o: Lit => (o.v == v) && (o.sign == sign)
    case _      => false
  }

  override def hashCode = v.hashCode + sign.hashCode

  def unary_- : Lit = Lit(v, !sign)

  def neg: Lit = -this

  def pos: Lit = this

  def dimacs = if (sign) -v else v
}
