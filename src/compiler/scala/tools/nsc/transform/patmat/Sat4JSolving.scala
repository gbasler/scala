/* NSC -- new Scala compiler
 *
 * @author Gerard Basler
 */

package scala.tools.nsc.transform.patmat

import scala.collection.mutable
import scala.reflect.internal.util.Statistics
import org.sat4j.specs.ContradictionException
import org.sat4j.specs.ISolver
import org.sat4j.minisat.SolverFactory
import org.sat4j.core.VecInt
import org.sat4j.specs.IVecInt
import org.sat4j.specs.IProblem
import org.sat4j.specs.IVec
import org.sat4j.minisat.constraints.cnf.Clauses
import scala.collection.immutable.Nil
import scala.annotation.tailrec


/**
 * Use ALL-SAT in order to check pattern matches for exhaustivity.
 *
 * Improvements vs copied code:
 * - don't need new variable for negation
 *
 * Comments to Adrian:
 * - Why not using lists and have immutable objects instead of buffers and state?
 */

trait Sat4JSolving extends Logic {

  import PatternMatchingStats._

  //    class FormulaBuilder {
  //      private[this] val problem = SolverFactory.newDefault
  //
  //      /** Adds a clause in the problem. */
  //      def +=(clause: IVecInt) = {
  //        problem addClause clause
  //        clause.clear
  //        this
  //      }
  //
  //      def solve: Status = {
  //        try {
  //          if (problem.isSatisfiable)
  //            Satisfiable
  //          else
  //            Unsatisfiable
  //        } catch {
  //          case _: Exception => Unknown
  //        }
  //      }
  //
  //      def model = {
  //        problem.model
  //      }
  //    }


  trait TseitinCNF extends PropositionalLogic with SolverInterface {

    import scala.collection.mutable.ArrayBuffer

    type FormulaBuilder = ArrayBuffer[FormulaForCNF]

    def formulaBuilder = ArrayBuffer[FormulaForCNF]()

    def addFormula(buff: FormulaBuilder, f: Formula): Unit = buff ++= f

    def toFormula(buff: FormulaBuilder): Formula = buff

    // TODO: a Formula is just a list of Formulae
    // (if we exposed CNF here directly, we can't efficiently build the conjunction)
    // alternative: expose CNF internals directly but simplifyFormula does then really make no sense
    // since it must happen _before_ Tseitin transformation
    type Formula = FormulaBuilder

    def andFormula(a: Formula, b: Formula): Formula = a ++ b

    def simplifyFormula(a: Formula) = a

    //    def cnfString(f: Formula) = alignAcrossRows(f map (_.toList) toList, "\\/", " /\\\n")

    def propToSolvable(p: Prop): Formula = {
      def formulaForProp(p: Prop): FormulaForCNF = p match {
        case And(a, b) => FormulaForCNF.And(formulaForProp(a), formulaForProp(b))
        case Or(a, b)  => FormulaForCNF.Or(formulaForProp(a), formulaForProp(b))
        case Not(a)    => FormulaForCNF.Not(formulaForProp(a))
        case True      => FormulaForCNF.True
        case False     => FormulaForCNF.False
        case sym: Sym  => FormulaForCNF.Var(sym)
      }

      val builder = formulaBuilder
      builder += formulaForProp(p)
      builder
    }

    def convert(f: Formula) = {
      type Cache = Map[FormulaForCNF, Lit]

      val cache = mutable.Map[FormulaForCNF, Lit]()

      val cnf = new Cnf

      def convertWithoutCache(f: FormulaForCNF): Lit = {
        f match {
          case FormulaForCNF.And(fv)   =>
            land(fv.map(convertWithCache))
          case FormulaForCNF.Or(fv)    =>
            lor(fv.map(convertWithCache))
          case FormulaForCNF.Not(a)    =>
            lnot(convertWithCache(a))
          case FormulaForCNF.Var(name) =>
            cnf.newLiteral()
          case FormulaForCNF.True      =>
            cnf.constTrue
          case FormulaForCNF.False     =>
            cnf.constFalse
        }
      }

      def convertWithCache(f: FormulaForCNF): Lit = {
        cache.get(f) match {
          case Some(lit) =>
            lit
          case None      =>
            val l = convertWithoutCache(f)
            require(cache.get(f) == None, "loop in formula?")
            cache += (f -> l)
            l
        }
      }

      def land(bv: Seq[Lit]): Lit = {
        // op1*op2*...*opx = c <==> (op1 + o')(op2 + o')... (opx + o')(op1' + op2' +... + opx' + o)
        import cnf._
        bv match {
          case Seq()                            => constTrue
          case Seq(l)                           => l
          case bv if bv.exists(_ == constFalse) => constFalse
          case bv if bv.forall(_ == constTrue)  => constTrue
          case bv                               =>
            val new_bv = bv.distinct.filterNot(_ == constTrue)
            val literal = newLiteral()
            new_bv.map(lit => lcnf(lit.pos, literal.neg))
            lcnf(new_bv.map(_.neg) :+ literal.pos: _*)
            literal
        }
      }

      def lor(ps: Seq[Lit]): Lit = {
        // op1+op2+...+opx = c <==> (op1' + o)(op2' + o)... (opx' + o)(op1 + op2 +... + opx + o')
        import cnf._
        ps match {
          case Seq()                            => constFalse
          case Seq(l)                           => l
          case bv if bv.exists(_ == constTrue)  => constTrue
          case bv if bv.forall(_ == constFalse) => constFalse
          case bv                               =>
            val new_bv = bv.distinct.filterNot(_ == constFalse)
            val literal = newLiteral()
            new_bv.map(lit => lcnf(lit.neg, literal.pos))
            lcnf(new_bv.map(_.pos) :+ literal.neg: _*)
            literal
        }
      }

      def lnot(a: Lit): Lit = -a

      def isAlreadyInCnf(f: FormulaForCNF): Option[Seq[Cnf#Clause]] = {
        import FormulaForCNF._

        def isDisjunction(f: FormulaForCNF): Option[Cnf#Clause] = f match {
          case FormulaForCNF.Or(fv) =>
            @tailrec
            def reduce(fv: List[FormulaForCNF] = fv.toList,
                       acc: Set[Lit] = Set()): Option[Set[Lit]] = fv match {
              case Nil      => Some(acc)
              case hd :: tl => isLiteral(hd) match {
                case Some(lit) => reduce(tl, acc + lit)
                case None      => None
              }
              case _        => None
            }
            reduce()

          case _ =>
            isLiteral(f).map(Set(_))
        }

        def isLiteral(f: FormulaForCNF): Option[Lit] = f match {
          case FormulaForCNF.Not(a)    =>
            isLiteral(a).map(_.neg)
          case v: FormulaForCNF.Var[_] =>
            Some(convertWithCache(f)) // go via cache in order to get single literal for variable
          case FormulaForCNF.True      =>
            Some(cnf.constTrue)
          case FormulaForCNF.False     =>
            Some(cnf.constFalse)
          case _                       =>
            None
        }

        f match {
          case FormulaForCNF.And(fv) =>
            @tailrec
            def reduce(fv: List[FormulaForCNF] = fv.toList,
                       acc: List[Cnf#Clause] = Nil): Option[Seq[Cnf#Clause]] = fv match {
              case Nil      => Some(acc)
              case hd :: tl => isDisjunction(hd) match {
                case Some(lit) => reduce(tl, lit :: acc)
                case None      => None
              }
              case _        => None
            }
            reduce()

          case _ =>
            isLiteral(f).map(l => Seq(Set(l)))
        }
      }

      f.foreach {
        f =>
          isAlreadyInCnf(f) match {
            case Some(clauses) =>
              clauses.foreach(cnf.addClause)
            case None          =>
              // add intermediate variable since we want the formula to be SAT!
              cnf.lcnf(convertWithCache(f))
          }
      }

      cnf.clauses
    }

    def findModelFor(f: Formula): Model

    def findAllModelsFor(f: Formula): List[Model]


    /** Returns true iff the given expression is already in conjunctive normal form. */
    //    def isAlreadyInCnf(f: Prop): (Boolean, Option[List[List[Prop]]]) = f match {
    //      case And(b1, b2) => {
    //        val (r1, l1) = isAlreadyInCnf(b1)
    //        if (r1) {
    //          val (r2, l2) = isAlreadyInCnf(b2)
    //          if (r2) (true, Some(l1.get ++ l2.get))
    //          else (false, None)
    //        } else (false, None)
    //      }
    //      case Or(b1, b2) => isDisjunction(f)
    //      case _          => isLiteral(f)
    //    }
    //
    //    def isDisjunction(f: Prop): (Boolean, Option[List[List[Prop]]]) = f match {
    //      case Or(b1, b2) => {
    //        val (r1, l1) = isDisjunction(b1)
    //        if (r1) {
    //          val (r2, l2) = isDisjunction(b2)
    //          if (r2) (true, Some(List(l1.get(0) ++ l2.get(0))))
    //          else (false, None)
    //        } else (false, None)
    //      }
    //      case _ => isLiteral(f)
    //    }


  }

  class Solver extends TseitinCNF {

    //    def isSat[U](problem: Formula): (Boolean, Option[Map[U, Boolean]]) = {
    //      try {
    //        val res = problem.solve
    //        res match {
    //          case Satisfiable => {
    //            val listeBoolExp = problem.model.toList map { x => if (x > 0) (litToSym(x) -> true) else (litToSym(-x) -> false) }
    //            val mapIdentBool = listeBoolExp filter (x => x match {
    //              case (s: AnonymousVariable, _) => false
    //              case (Lit(_), _)             => true
    //              case _                         => false
    //            })
    //            val mapUBool = mapIdentBool map (z => z match {
    //              case (Lit(s), b) => (s, b)
    //              case _                => throw new IllegalStateException
    //            })
    //            (true, Some(mapUBool.toMap))
    //          }
    //          case Unsatisfiable => (false, None)
    //          case _             => throw new IllegalStateException("Got a time out")
    //        }
    //      } catch {
    //        case e: ContradictionException => (false, None)
    //      }
    //    }


  }

}

