/* NSC -- new Scala compiler
 *
 * @author Gerard Basler
 */

package scala.tools.nsc.transform.patmat

import scala.collection.mutable
import org.sat4j.specs.{IVec, IVecInt, TimeoutException, ContradictionException}
import org.sat4j.minisat.SolverFactory
import org.sat4j.core.{Vec, VecInt}
import scala.annotation.tailrec
import org.sat4j.tools.ModelIterator

/**
 * Use ALL-SAT in order to check pattern matches for exhaustivity.
 *
 * The Tseitin transformation trades an exponential blow-up
 * in formula size for additional variables (linear).
 *
 * Improvements vs copied code:
 * - don't need new variable for negation
 *
 * Comments to Adrian:
 * - Why not using lists and have immutable objects instead of buffers and state?
 */

trait Sat4JSolving extends Logic {

  trait TseitinCNF extends PropositionalLogic with SolverInterface {

    object SATSolverBudget {

      abstract class Exception(val advice: String) extends RuntimeException("SAT solver error")

      object timeout extends Exception(
        s"(The SAT solver run into a timeout. Please report a simplified example to JIRA.")

    }

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

    def cnfString(f: Formula): String = {
      val cnf = convert(f)._1
      cnf.dimacs
    }

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

    def convert(f: Formula): (Cnf, Map[Sym, Lit]) = {
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

      // all variables are guaranteed to be in cache
      // (doesn't mean they will appear in the resulting formula)
      val litForSym: Map[Sym, Lit] = {
        cache.collect {
          case (v: FormulaForCNF.Var[_], lit) => v.sym.asInstanceOf[Sym] -> lit
        }
      }.toMap

      (cnf, litForSym)
    }

  }

  class SatSolver extends TseitinCNF {

    val EmptyModel = Map.empty[Sym, Boolean]
    val NoModel: Model = null

    def findModelFor(f: Formula): Model = {
      val (cnf, litForSym) = convert(f)

      val solver = new ModelIterator(SolverFactory.newDefault())

      solver.addAllClauses(clausesForCnf(cnf))

      try {
        if (solver.isSatisfiable()) {
          val model: Array[Int] = solver.model()

          // don't check intermediate vars
          val model0 = model.toSet
          require(model.length == model0.size, "literal lost")

          def polarityForLiteral(lit: Lit) = {
            if (model0.contains(lit.v)) {
              true
            } else if (model0.contains(-lit.v)) {
              false
            } else {
              // literal has no influence on formula
              sys.error(s"Literal not found ${lit} (should assume nondet)")
            }
          }

          litForSym.map {
            case (v, l) => v -> polarityForLiteral(l)
          }.toMap
        } else {
          NoModel
        }
      } catch {
        case e: ContradictionException =>
          // constant propagation should prevent this from happening
          sys.error("Formula trivially UNSAT, should not happen, please report error.")
        case e: TimeoutException       =>
          throw SATSolverBudget.timeout
      }
    }

    def findAllModelsFor(f: Formula): List[Model] = {
      val (cnf, litForSym) = convert(f)

      val solver = new ModelIterator(SolverFactory.newDefault())

      solver.addAllClauses(clausesForCnf(cnf))

      try {
        @tailrec
        def allModels(acc: List[Model] = Nil): List[Model] = if (solver.isSatisfiable()) {
          val model: Array[Int] = solver.model()

          // don't check intermediate vars
          val model0 = model.toSet
          require(model.length == model0.size, "literal lost")

          def polarityForLiteral(lit: Lit) = {
            if (model0.contains(lit.v)) {
              true
            } else if (model0.contains(-lit.v)) {
              false
            } else {
              // literal has no influence on formula
              sys.error(s"Literal not found ${lit} (should assume nondet)")
            }
          }

          val valuation: Model = litForSym.map {
            case (v, l) => v -> polarityForLiteral(l)
          }.toMap
          allModels(valuation :: acc)
        } else {
          acc
        }
        allModels()
      } catch {
        case e: ContradictionException =>
          // constant propagation should prevent this from happening
          sys.error("Formula trivially UNSAT, should not happen, please report error.")
        case e: TimeoutException       =>
          throw SATSolverBudget.timeout
      }
    }

    private def clausesForCnf(cnf: Cnf): IVec[IVecInt] = {
      val clauses: Array[IVecInt] = cnf.clauses.map(clause => new VecInt(clause.map(_.dimacs).toArray)).toArray
      new Vec(clauses)
    }
  }

}

