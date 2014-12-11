package scala.tools.nsc.transform.patmat

import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4
import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.tools.nsc.{Global, Settings}

object TestSolver extends Logic with Solving {

  val global: Global = new Global(new Settings())

  object TestSolver extends Solver {

    class Const {
      override def toString: String = "Const"
    }
    val NullConst = new Const;
    type Type = Int;

    case class TypeConst(i: Int) extends Const;

    object TypeConst extends TypeConstExtractor;

    case class ValueConst(i: Int) extends Const;

    object ValueConst extends ValueConstExtractor {
      def apply(t: Tree): Const = ???
    };

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

      def domainSyms = None;

      def implications = Nil;

      def mayBeNull = false;

      def propForEqualsTo(c: Const): Prop = ???;

      def registerEquality(c: Const) = ();

      def registerNull() = ();

      def symForStaticTp = None
    }

    object Var extends VarExtractor {
      def apply(x: Tree): Var = new Var(x)

      def unapply(v: Var): Some[Tree] = Some(v.x)
    };

    def prepareNewAnalysis = {};

    def reportWarning(msg: String) = sys.error(msg)

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

  @Test
  def test2: Unit = {
    import TestSolver.TestSolver._
    val p: Var = Var(Tree("p"))
    val f = Or(Sym(p, NullConst), Not(Sym(p, NullConst)))
    val solvable = propToSolvable(f)
    val solutions = TestSolver.TestSolver.findAllModelsFor(solvable)
    val models = solutions.map(_.model)
    val expected = Seq(
      Map(p -> false),
      Map(p -> true)
    )
    println(solutions)
    assertEquals(expected.toSet, models.toSet)
  }
}


