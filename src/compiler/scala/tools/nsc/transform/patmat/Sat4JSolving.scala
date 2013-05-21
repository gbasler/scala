/* NSC -- new Scala compiler
 *
 * @author Gerard Basler
 */

package scala.tools.nsc.transform.patmat

import scala.collection.mutable
import org.sat4j.minisat.SolverFactory
import org.sat4j.core.{Vec, VecInt}
import scala.annotation.tailrec
import org.sat4j.tools.ModelIterator
import org.sat4j.specs.{IVecInt, IVec, ISolver, TimeoutException, ContradictionException}

/**
 * Use ALL-SAT in order to check pattern matches for exhaustivity.
 *
 * The Tseitin transformation trades an exponential blow-up
 * in formula size for additional variables (linear).
 * (Using the Plaisted transformation would reduce formula size but
 * all models will be found twice, if one polarity has been removed,
 * so no improvement).
 * Further improvements might be achieved by using a transformation
 * that decides (via a cost function) when to prefer expanding over
 * introducing additional variables.
 *
 *
 * Comments to Adriaan:
 * - Code is not very functional, why not using lists and have immutable objects instead of buffers and state?
 *
 * Improvements vs copied code (I removed it, it was plain ugly):
 * - don't use a new variable for negation
 * - share subgraphs (reduces formula size)
 * - flatten trees of same connectives (avoids unnecessary variables)
 *
 * Currently this regression test fails:
 * /files/neg/patmatexhaust.scala
 *
 * One line of the output changes:
 * < It would fail on the following inputs: C(), D1, D2()
 * ---
 * > It would fail on the following inputs: D1, D2()
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
              val simplified = FormulaForCNF.simplify(f)
              // add intermediate variable since we want the formula to be SAT!
              cnf.lcnf(convertWithCache(simplified))
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

      try {
        solver.addAllClauses(clausesForCnf(cnf))

        if (solver.isSatisfiable()) {
          extractModel(solver, litForSym)
        } else {
          NoModel
        }
      } catch {
        case e: ContradictionException =>
          // TODO not sure if it's ok for this to happen since we have constant propagation
          NoModel
        case e: TimeoutException       =>
          throw SATSolverBudget.timeout
      }
    }

    def findAllModelsFor(f: Formula): List[Model] = {
      val (cnf, litForSym) = convert(f)

      val solver: ModelIterator = new ModelIterator(SolverFactory.newDefault())

      try {
        @tailrec
        def allModels(acc: List[Model] = Nil): List[Model] = if (solver.isSatisfiable()) {
          val valuation = extractModel(solver, litForSym)
          allModels(valuation :: acc)
        } else {
          acc
        }

        solver.addAllClauses(clausesForCnf(cnf))

        allModels()
      } catch {
        case e: ContradictionException =>
          // TODO not sure if it's ok for this to happen since we have constant propagation
          Nil
        case e: TimeoutException       =>
          throw SATSolverBudget.timeout
      }
    }

    private def clausesForCnf(cnf: Cnf): IVec[IVecInt] = {
      val clauses: Array[IVecInt] = cnf.clauses.map(clause => new VecInt(clause.map(_.dimacs).toArray)).toArray
      new Vec(clauses)
    }

    private def extractModel(solver: ISolver, litForSym: Map[Sym, Lit]) = {
      val model = solver.model()

      // don't check intermediate vars
      val model0 = model.toSet
      require(model.length == model0.size, "literal lost")

      object PolarityForLiteral {
        def unapply(lit: Lit): Option[Boolean] = {
          if (model0.contains(lit.v)) {
            Some(true)
          } else if (model0.contains(-lit.v)) {
            Some(false)
          } else {
            // literal has no influence on formula
            // sys.error(s"Literal not found ${lit} (should assume nondet)")
            // (if uncommented this error causes the regression tests to fail)
            // TODO: not sure if just omitting is causing other problems
            None
          }
        }
      }

      litForSym.collect {
        case (v, l@PolarityForLiteral(polarity)) => v -> polarity
      }.toMap
    }
  }

}

