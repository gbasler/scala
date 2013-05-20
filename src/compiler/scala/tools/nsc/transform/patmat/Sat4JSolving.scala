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




/**
 * Use ALL-SAT in order to check pattern matches for exhaustivity.
 *
 * Improvements vs copied code:
 * - don't need new variable for negation
 *
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
    def formulaBuilder  = ArrayBuffer[FormulaForCNF]()
    def addFormula(buff: FormulaBuilder, f: Formula): Unit = buff ++= f
    def toFormula(buff: FormulaBuilder): Formula = buff

    // TODO: a Formula is just a list of Formulae
    // (if we exposed CNF here directly, we can't efficiently build the conjunction)
    // alternative: expose CNF internals directly but simplifyFormula does then really make no sense
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

