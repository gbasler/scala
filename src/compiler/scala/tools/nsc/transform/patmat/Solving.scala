/* NSC -- new Scala compiler
 *
 * Copyright 2011-2013 LAMP/EPFL
 * @author Adriaan Moors
 */

package scala.tools.nsc.transform.patmat

import regolic.sat.Solver
import regolic.sat.Solver.{Results, Clause}
import regolic.Settings
import scala.reflect.internal.util.Statistics
import scala.language.postfixOps
import scala.annotation.tailrec
import scala.collection.mutable

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

  trait TseitinCNF extends PropositionalLogic {

    def eqFreePropToSolvable(p: Prop): Solvable = {
      type Cache = Map[Prop, Lit]

      val cache = mutable.Map[Prop, Lit]()

      val cnf = new CNF

      def convertWithoutCache(p: Prop): Lit = {
        p match {
          case And(fv)   =>
            // TODO This will probably result in outer checks for the matches (unless the nested classes are final). Best to double check the bytecode.
            and(fv.map(convertWithCache))
          case Or(fv)    =>
            or(fv.map(convertWithCache))
          case Not(a)    =>
            not(convertWithCache(a))
          case Sym(_, _) =>
            cnf.newLiteral()
          case True      =>
            cnf.constTrue
          case False     =>
            cnf.constFalse
          case Eq(_, _)  =>
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
          case Sym(_, _) =>
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
          case p      =>
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
          case p       =>
            ToDisjunction.unapply(p).map(Seq(_))
        }
      }

      val simplified = simplify(p)
      simplified match {
        case ToCnf(clauses) =>
          // already in CNF, just add clauses
          clauses.foreach(cnf.addClauseRaw)
        case p              =>
          // add intermediate variable since we want the formula to be SAT!
          cnf.addClauseProcessed(convertWithCache(p))
      }

      // all variables are guaranteed to be in cache
      // (doesn't mean they will appear in the resulting formula)
      val litForSym: Map[Sym, Lit] = cache.collect {
        case (sym: Sym, lit) => sym -> lit
      }(collection.breakOut) // breakOut in order to obtain immutable Map
      // TODO: replace cache with monadic structure

      Solvable(cnf, litForSym)
    }

  }

  // simple wrapper around a SAT solver
  trait SatSolver extends TseitinCNF {

    // adapted from http://lara.epfl.ch/w/sav10:simple_sat_solver (original by Hossein Hojjat)
    val EmptyModel = Map.empty[Sym, Boolean]
    val NoModel: Model = null

    def findModelFor(solvable: Solvable, timeout: Int): Model = {
      import solvable._
      debug.patmat(s"searching for one model for:\n${cnf.dimacs}")

      val start = if (Statistics.canEnable) Statistics.startTimer(patmatAnaSAT) else null

      Settings.timeout = Some(timeout)
      val result = Solver.solve(clausesForCnf(cnf), cnf.noLiterals + 1)
      val satisfiableWithModel = result match {
        case Results.Satisfiable(model) =>
          extractModel(model, litForSym)
        case _                          =>
          NoModel
      }
      if (Statistics.canEnable) Statistics.stopTimer(patmatAnaSAT, start)

      satisfiableWithModel
    }

    // returns all solutions, if any
    def findAllModelsFor(solvable: Solvable, timeout: Int): List[Model] = {
      import solvable._
      debug.patmat(s"searching for all models for:\n${cnf.dimacs}")

      Settings.timeout = Some(timeout)
      import scala.reflect.internal.util.Statistics
      import scala.tools.nsc.transform.patmat.PatternMatchingStats._

      val start = if (Statistics.canEnable) Statistics.startTimer(patmatAnaSAT) else null

      @tailrec
      def allModels(clauses: List[Clause], acc: List[Model] = Nil): List[Model] = {
        val result = Solver.solve(clauses, cnf.noLiterals + 1)
        result match {
          case Results.Satisfiable(model) =>
            val valuation = extractModel(model, litForSym)
            val blockingClause = for {
              (sym, value) <- valuation
            } yield {
              if (value) {
                litForSym(sym).dimacs
              } else {
                litForSym(sym).neg.dimacs
              }
            }
            allModels(new Clause(blockingClause.toArray) :: clauses, valuation :: acc)
          case _                          =>
            acc
        }
      }
      val models = allModels(clausesForCnf(cnf))
      if (Statistics.canEnable) Statistics.stopTimer(patmatAnaSAT, start)
      models
    }

    private def clausesForCnf(cnf: CNF) = {
      cnf.clauses.map(clause => new Clause(clause.toList))
    }

    private def extractModel(model: Array[Boolean], litForSym: Map[Sym, Lit]) = {

      object PolarityForLiteral {
        def unapply(lit: Lit): Option[Boolean] = {
          Some(!model(lit.v))
        }
      }

      // don't extract intermediate literals
      litForSym.collect {
        case (v, PolarityForLiteral(polarity)) => v -> polarity
      }
    }
  }
}
