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

    def prepareNewAnalysis = {}

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
  //  @Test
  //  def test1: Unit = {
  //    import TestSolver.TestSolver._
  //    val f = Or(True, False)
  //    //    val f = Or(Var("p"), Not(Var("p")))
  //    //          val models = allTseitinModels(f)
  //    val solvable = propToSolvable(f)
  //    val solutions = TestSolver.TestSolver.findAllModelsFor(solvable)
  //    println(solutions)
  //    //    assert(2 + 2 == 5, "you didn't get the math right fellow")
  //    assertTrue("you didn't get the math right fellow", 2 + 2 == 4)
  //  }

  import TestSolver.TestSolver._

  implicit val Ord: Ordering[TestSolver.TestSolver.Model] = Ordering.by {
    _.toSeq.sortBy(_.toString()).toIterable
  }

  @Test
  def testUnassigned() ni{
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


