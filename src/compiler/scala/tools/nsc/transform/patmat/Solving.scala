/* NSC -- new Scala compiler
 *
 * Copyright 2011-2013 LAMP/EPFL
 * @author Adriaan Moors
 */

package scala.tools.nsc.transform.patmat

import scala.reflect.internal.util.Statistics
import scala.language.postfixOps
import org.sat4j.tools.ModelIterator
import org.sat4j.minisat.SolverFactory
import scala.annotation.tailrec
import org.sat4j.specs.ContradictionException
import org.sat4j.specs.TimeoutException
import org.sat4j.specs.IVec
import org.sat4j.specs.IVecInt
import org.sat4j.core.VecInt
import org.sat4j.core.Vec
import org.sat4j.specs.ISolver
import scala.collection.mutable

/**
 * Solve pattern matcher exhaustivity problem via SAT solver.
 */
trait Solving extends Logic {

  private def traverse[A, B](a: List[A])(f: A => Option[B]): Option[List[B]] =
    a match {
      case Nil    =>
        Some(Nil)
      case h :: t =>
        for {
          a1 <- f(h)
          b1 <- traverse(t)(f)
        } yield a1 :: b1
    }

  import PatternMatchingStats._

  /**
   * Tseitin transformation: used for conversion of a
   * propositional formula into conjunctive normal form (CNF)
   * (input format for SAT solver).
   * A simple conversion into CNF via Shannon expansion would
   * also be possible but it's worst-case complexity is exponential
   * (in the number of variables) and thus even simple problems
   * could become untractable.
   * The Tseitin transformation results in an _equisatisfiable_
   * CNF-formula (it generates auxiliary variables)
   * but runs with linear complexity.
   */
  trait TseitinCNF extends PropositionalLogic {

    def eqFreePropToSolvable(p: Prop): Solvable = {
      type Cache = Map[Prop, Lit]

      val cache = mutable.Map[Prop, Lit]()

      val cnf = new CNF

      def convertWithoutCache(p: Prop): Lit = {
        p match {
          case And(fv)   =>
            and(fv.map(convertWithCache))
          case Or(fv)    =>
            or(fv.map(convertWithCache))
          case Not(a)    =>
            not(convertWithCache(a))
          case _: Sym =>
            cnf.newLiteral()
          case True      =>
            cnf.constTrue
          case False     =>
            cnf.constFalse
          case _: Eq =>
            sys.error("Forgot to call propToSolvable()?")
        }
      }

      def convertWithCache(p: Prop): Lit = {
        cache.getOrElse(p, {
          val l = convertWithoutCache(p)
          require(!cache.isDefinedAt(p), "loop in formula?")
          cache += (p -> l)
          l
        })
      }

      def and(bv: Set[Lit]): Lit = {
        import cnf._
        if (bv.isEmpty) {
          constTrue
        } else if (bv.size == 1) {
          bv.head
        } else if (bv.contains(constFalse)) {
          constFalse
        } else {
          // op1*op2*...*opx <==> (op1 + o')(op2 + o')... (opx + o')(op1' + op2' +... + opx' + o)
          val new_bv = bv - constTrue // ignore `True`
          val o = newLiteral() // auxiliary Tseitin variable
          new_bv.map(op => addClauseProcessed(op.pos, o.neg))
          addClauseProcessed((new_bv.map(_.neg) + o.pos).toSeq: _*)
          o
        }
      }

      def or(bv: Set[Lit]): Lit = {
        import cnf._
        if (bv.isEmpty) {
          constFalse
        } else if (bv.size == 1) {
          bv.head
        } else if (bv.contains(constTrue)) {
          constTrue
        } else {
          // op1+op2+...+opx <==> (op1' + o)(op2' + o)... (opx' + o)(op1 + op2 +... + opx + o')
          val new_bv = bv - constFalse // ignore `False`
          val o = newLiteral() // auxiliary Tseitin variable
          new_bv.map(op => addClauseProcessed(op.neg, o.pos))
          addClauseProcessed((new_bv.map(_.pos) + o.neg).toSeq: _*)
          o
        }
      }

      // no need for auxiliary variable
      def not(a: Lit): Lit = -a

      object ToLiteral {
        def unapply(f: Prop): Option[Lit] = f match {
          case Not(a)    =>
            ToLiteral.unapply(a).map(_.neg)
          case _: Sym =>
            Some(convertWithCache(f)) // go via cache in order to get single literal for variable
          case True      =>
            Some(cnf.constTrue)
          case False     =>
            Some(cnf.constFalse)
          case _         =>
            None
        }
      }

      object ToDisjunction {
        def unapply(p: Prop): Option[CNF#Clause] = p match {
          case Or(fv) =>
            traverse(fv.toList)(ToLiteral.unapply).map(_.toSet)
          case p =>
            ToLiteral.unapply(p).map(Set(_))
        }
      }

      /**
       * Checks if propositional formula is already in CNF
       */
      object ToCnf {
        def unapply(f: Prop): Option[Seq[CNF#Clause]] = f match {
          case And(fv) =>
            traverse(fv.toList)(ToDisjunction.unapply).map(_.toSeq)
          case p =>
            ToDisjunction.unapply(p).map(Seq(_))
        }
      }

      val simplified = simplify(p)
      simplified match {
        case ToCnf(clauses) =>
          // already in CNF, just add clauses
          clauses.foreach(cnf.addClauseRaw)
        case p                       =>
          // add intermediate variable since we want the formula to be SAT!
          cnf.addClauseProcessed(convertWithCache(p))
      }

      // all variables are guaranteed to be in cache
      // (doesn't mean they will appear in the resulting formula)
      val litForSym: Map[Sym, Lit] = cache.collect {
        case (sym: Sym, lit) => sym -> lit
      }(collection.breakOut) // breakOut in order to obtain immutable Map

      Solvable(cnf, litForSym)
    }

  }

  // simple wrapper around a SAT solver
  trait SatSolver extends TseitinCNF {

    val EmptyModel = Map.empty[Sym, Boolean]
    val NoModel: Model = null

    def findModelFor(solvable: Solvable, timeout: Long): Model = {
      import solvable._
      debug.patmat(s"searching for one model for:\n${cnf.dimacs}")

      val start = if (Statistics.canEnable) Statistics.startTimer(patmatAnaSAT) else null

      val solver = SolverFactory.newDefault()
      solver.setTimeoutMs(timeout)

      val satisfiableWithModel: Model = try {
        solver.addAllClauses(clausesForCnf(cnf))

        if (solver.isSatisfiable()) {
          extractModel(solver, litForSym)
        } else {
          NoModel
        }
      } catch {
        case _: ContradictionException =>
          // TODO not sure if it's ok for this to happen since we have constant propagation
          NoModel
        case _: TimeoutException       =>
          throw AnalysisBudget.timeout
      }

      if (Statistics.canEnable) Statistics.stopTimer(patmatAnaSAT, start)

      satisfiableWithModel
    }

    // returns all solutions, if any
    def findAllModelsFor(solvable: Solvable, timeout: Long): List[Model] = {
      import solvable._
      debug.patmat(s"searching for all models for:\n${cnf.dimacs}")

      val solver: ModelIterator = new ModelIterator(SolverFactory.newDefault())
      solver.setTimeoutMs(timeout)

      import scala.reflect.internal.util.Statistics
      import scala.tools.nsc.transform.patmat.PatternMatchingStats._

      val start = if (Statistics.canEnable) Statistics.startTimer(patmatAnaSAT) else null
      val models = try {
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
        case _: ContradictionException =>
          // TODO not sure if it's ok for this to happen since we have constant propagation
          Nil
        case _: TimeoutException       =>
          throw AnalysisBudget.timeout
      }

      if (Statistics.canEnable) Statistics.stopTimer(patmatAnaSAT, start)
      models
    }

    private def clausesForCnf(cnf: CNF): IVec[IVecInt] = {
      val clauses: Array[IVecInt] = cnf.clauses.map(clause => new VecInt(clause.map(_.dimacs).toArray))
      new Vec(clauses)
    }

    private def extractModel(solver: ISolver, litForSym: Map[Sym, Lit]) = {
      val model = solver.model()

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

      // don't extract intermediate literals
      litForSym.collect {
        case (v, PolarityForLiteral(polarity)) => v -> polarity
      }
    }
  }
}
