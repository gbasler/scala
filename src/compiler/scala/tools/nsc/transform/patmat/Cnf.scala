/* NSC -- new Scala compiler
 *
 * @author Gerard Basler
 */

package scala.tools.nsc.transform.patmat

class Cnf {

  import scala.collection.mutable.ArrayBuffer

  type Clause = Set[Lit]
  type ClauseBuilder = ArrayBuffer[Clause]

  var noLiterals = 0

  val buff = ArrayBuffer[Clause]()

  def addClause(clause: Clause): Unit = buff += clause

  def clauses: Seq[Clause] = buff.toSeq

  override def toString: String = {
    {
      for {
        clause <- buff
      } yield {
        clause.mkString("(", " ", ")")
      }
    }.mkString("\n")
  }

  def dimacs: String = {
    val header = s"p cnf ${noLiterals} ${buff.length}\n"
    header + {
      for {
        clause <- buff
      } yield {
        clause.mkString("", " ", " 0")
      }
    }.mkString("\n")
  }

  def newLiteral(): Lit = {
    noLiterals += 1
    Lit(noLiterals, false)
  }

  val constTrue: Lit = {
    val constTrue = newLiteral()
    lcnf(constTrue.pos)
    constTrue
  }

  val constFalse: Lit = -constTrue

  def isConst(l: Lit): Boolean = l == constTrue || l == constFalse

  def lcnf(bv: Lit*) {
    val clause = processClause(bv: _*)
    if (clause.nonEmpty)
      addClause(clause)
  }

  /**
   * @return empty clause, if clause trivially satisfied
   */
  def processClause(bv: Lit*): Clause = {
    val clause = bv.distinct

    val isTautology = clause.combinations(2).exists {
      case Seq(a, b) => a == -b
    }

    if (isTautology)
      Set()
    else
      clause.toSet
  }
}
