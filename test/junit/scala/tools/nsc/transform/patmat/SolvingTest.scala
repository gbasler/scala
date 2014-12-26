package scala.tools.nsc.transform.patmat

import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4
import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.collection.mutable
import scala.tools.nsc.transform.patmat.TestSolver
import scala.tools.nsc.{Global, Settings}

object TestSolver extends Logic with Solving {

  val global: Global = new Global(new Settings())

  object TestSolver extends Solver {

    class Const {
      override def toString: String = "Const"
    }

    val NullConst = new Const
    type Type = Int

    case class TypeConst(i: Int) extends Const

    object TypeConst extends TypeConstExtractor

    case class ValueConst(i: Int) extends Const

    object ValueConst extends ValueConstExtractor {
      def apply(t: Tree): Const = ???
    }

    case class Tree(name: String)

    class Var(val x: Tree) extends AbsVar {

      override def equals(o: scala.Any): Boolean = {
        o match {
          case other: Var => this.x == other.x
          case _ => false
        }
      }

      override def hashCode(): Int = x.hashCode()

      override def toString: String = {
        s"Var($x)"
      }

      def domainSyms = None

      def implications = Nil

      def mayBeNull = false

      def propForEqualsTo(c: Const): Prop = ???

      def registerEquality(c: Const) = ()

      def registerNull() = ()

      def symForStaticTp = None
    }

    object Var extends VarExtractor {
      def apply(x: Tree): Var = new Var(x)

      def unapply(v: Var): Some[Tree] = Some(v.x)
    }

    def prepareNewAnalysis() = {}

    def reportWarning(msg: String) = sys.error(msg)

    /**
     * The DPLL procedure only returns a minimal mapping from literal to value
     * such that the CNF formula is satisfied.
     * E.g. for:
     * `(a \/ b)`
     * The DPLL procedure will find either {a = true} or {b = true}
     * as solution.
     *
     * The expansion step will amend both solutions with the unassigned variable
     * i.e., {a = true} will be expanded to {a = true, b = true} and {a = true, b = false}.
     */
    def expandUnassigned(solution: Solution): List[Model] = {
      import solution._

      // the number of solutions is doubled for every unassigned variable
      val expandedModels = 1 << unassigned.size
      var current = mutable.ArrayBuffer[Model]()
      var next = mutable.ArrayBuffer[Model]()
      current.sizeHint(expandedModels)
      next.sizeHint(expandedModels)

      current += model

      // we use double buffering:
      // read from `current` and create a two models for each model in `next`
      for {
        s <- unassigned
      } {
        for {
          model <- current
        } {
          def force(s: Sym, pol: Boolean) = model + (s -> pol)

          next += force(s, pol = true)
          next += force(s, pol = false)
        }

        val tmp = current
        current = next
        next = tmp

        next.clear()
      }

      current.toList
    }

    def eqFreePropToSolvableByExpansion(p: Prop) = {
      val symbolMapping = new SymbolMapping(gatherSymbols(p))

      type Formula = Array[TestSolver.Clause]

      def formula(c: Clause*): Formula = c.toArray

      def merge(a: Clause, b: Clause) = a ++ b

      def negationNormalFormNot(p: Prop): Prop = p match {
        case And(ps) => Or(ps map negationNormalFormNot)
        case Or(ps) => And(ps map negationNormalFormNot)
        case Not(p) => negationNormalForm(p)
        case True => False
        case False => True
        case s: Sym => Not(s)
      }

      def negationNormalForm(p: Prop): Prop = p match {
        case Or(ps) => Or(ps map negationNormalForm)
        case And(ps) => And(ps map negationNormalForm)
        case Not(negated) => negationNormalFormNot(negated)
        case True
             | False
             | (_: Sym) => p
      }

      val TrueF: Formula = Array()
      val FalseF = Array(clause())
      def lit(sym: Sym) = Array(clause(symbolMapping.lit(sym)))
      def negLit(sym: Sym) = Array(clause(-symbolMapping.lit(sym)))

      def conjunctiveNormalForm(p: Prop): Formula = {
        def distribute(a: Formula, b: Formula): Formula =
          (a, b) match {
            // true \/ _ = true
            // _ \/ true = true
            case (trueA, trueB) if trueA.size == 0 || trueB.size == 0 => TrueF
            // lit \/ lit
            case (a, b) if a.size == 1 && b.size == 1 => formula(merge(a(0), b(0)))
            // (c1 /\ ... /\ cn) \/ d = ((c1 \/ d) /\ ... /\ (cn \/ d))
            // d \/ (c1 /\ ... /\ cn) = ((d \/ c1) /\ ... /\ (d \/ cn))
            case (cs, ds) =>
              val (big, small) = if (cs.size > ds.size) (cs, ds) else (ds, cs)
              big flatMap (c => distribute(formula(c), small))
          }

        p match {
          case True => TrueF
          case False => FalseF
          case s: Sym => lit(s)
          case Not(s: Sym) => negLit(s)
          case And(ps) =>
            ps.toArray flatMap conjunctiveNormalForm
          case Or(ps) =>
            ps map conjunctiveNormalForm reduceLeft { (a, b) =>
              distribute(a, b)
            }
        }
      }
      val cnf = conjunctiveNormalForm(negationNormalForm(p))
      Solvable(cnf, symbolMapping)
    }

    //    def assertModels(expected: Seq[Model], actual: Seq[Model]) = {
    //      assertEquals(expected.length, actual.length)
    //      for {
    //        ma <- actual
    //      } yield {
    //        ma.find {
    //          case (sym: TestSolver.Sym, b: Boolean) =>
    //          case (m: Model) => b must contain(m)
    //
    //        }
    //      }
    //    }

  }

}

/** Sample JUnit test that shows that all pieces
    of JUnit infrastructure work correctly */
@RunWith(classOf[JUnit4])
class SolvingTest {

  import TestSolver.TestSolver._

  implicit val Ord: Ordering[TestSolver.TestSolver.Model] = Ordering.by {
    _.toSeq.sortBy(_.toString()).toIterable
  }

  @Test
  def testUnassigned() {
    val pSym = Sym(Var(Tree("p")), NullConst)
    val solvable = propToSolvable(Or(pSym, Not(pSym)))
    val solutions = TestSolver.TestSolver.findAllModelsFor(solvable)
    val expected = List(Solution(Map(), List(pSym)))
    assertEquals(expected, solutions)
  }

  @Test
  def testUnassignedWithExpansion() {
    val pSym = Sym(Var(Tree("p")), NullConst)
    val qSym = Sym(Var(Tree("q")), NullConst)
    val solvable = propToSolvable(Or(pSym, Not(qSym)))
    val solutions = findAllModelsFor(solvable)
    val expanded = solutions.flatMap(expandUnassigned).sorted
    val expected = Seq(
      Map(pSym -> false, qSym -> false),
      Map(pSym -> true, qSym -> false),
      Map(pSym -> true, qSym -> true)
    ).sorted

    assertEquals(expected, expanded)
  }

  @Test
  def testTseitinVsShannon() {
    val pSym = Sym(Var(Tree("p")), NullConst)
    val qSym = Sym(Var(Tree("q")), NullConst)
    val f1 = And(pSym, Not(qSym))
    val f2 = And(Not(pSym), qSym)
    val f = Or(f1, f2)
    val s1 = propToSolvable(f)
    val solutions = findAllModelsFor(s1)
    val s2 = eqFreePropToSolvableByExpansion(f)
    //    println(s1.cnf.mkString("\n"))
    //    println("***********")
    //    println(s2.cnf.mkString("\n"))
    val solutions2 = findAllModelsFor(s2)
    val expanded = solutions.flatMap(expandUnassigned).sorted
    val expanded2 = solutions2.flatMap(expandUnassigned).sorted
    assertEquals(expanded, expanded2)
  }

  @Test
  def test3: Unit = {
    import TestSolver.TestSolver._
    val p: Var = Var(Tree("p"))
    val pSym: TestSolver.TestSolver.Sym = Sym(p, NullConst)
    val f = Or(pSym, Not(pSym))
    val solvable = propToSolvable(f)
    val solutions: List[TestSolver.TestSolver.Solution] = TestSolver.TestSolver.findAllModelsFor(solvable)
    val models = solutions.map(_.model)
    val expected = Seq(
      Map(p -> false),
      Map(p -> true)
    )
    val expected2 = List(Solution(Map(), List(pSym)))
    //    println(solutions.mkString("\n"))
    //    println(models.mkString("\n"))
    //    println(expected)
    //    assertEquals(expected.toSet, models.toSet)
    assertEquals(expected2, solutions)
  }
}


