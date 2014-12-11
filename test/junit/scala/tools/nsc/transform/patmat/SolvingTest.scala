package scala.tools.nsc.transform.patmat

import scala.tools.nsc.{Global, Settings}

object TestSolver extends Logic with Solving {

  val global: Global = new Global(new Settings())

  object TestSolver extends Solver {

    class Const;
    val NullConst = new Const;
    type Type = Int;

    case class TypeConst(i: Int) extends Const;

    object TypeConst extends TypeConstExtractor;

    case class ValueConst(i: Int) extends Const;

    object ValueConst extends ValueConstExtractor {
      def apply(t: Tree): Const = ???
    };

    class Tree;

    class Var(val x: Tree) extends AbsVar {
      def domainSyms = None;

      def implications = Nil;

      def mayBeNull = false;

      def propForEqualsTo(c: Const): Prop = ???;

      def registerEquality(c: Const) = ();

      def registerNull() = ();

      def symForStaticTp = None
    };

    object Var extends VarExtractor {
      def apply(x: Tree): Var = ???;

      def unapply(v: Var): Some[Tree] = Some(v.x)
    };

    def prepareNewAnalysis = {};

    def reportWarning(msg: String) = sys.error(msg)
  }

}

///** Sample JUnit test that shows that all pieces
//    of JUnit infrastructure work correctly */
//@RunWith(classOf[JUnit4])
//class SolvingTest {
//  @Test
//  def testMath: Unit = {
//    assert(2 + 2 == 4, "you didn't get the math right fellow")
//  }
//}


