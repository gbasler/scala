/* NSC -- new Scala compiler
 *
 * Copyright 2011-2013 LAMP/EPFL
 * @author Adriaan Moors
 */

package scala.tools.nsc.transform.patmat

import scala.collection
import scala.collection.immutable.SortedSet
import scala.reflect.internal.util.Statistics
import scala.language.postfixOps
import scala.collection.mutable
import scala.Some
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

/** Solve pattern matcher exhaustivity problem via DPLL.
 */
trait Solving extends Logic {

  /** Tseitin transformation: used for conversion of a
   *  propositional formula into conjunctive normal form (CNF)
   *  (input format for SAT solver).
   *  A simple conversion into CNF via Shannon expansion would
   *  also be possible but it's worst-case complexity is exponential
   *  (in the number of variables) and thus even simple problems
   *  could become untractable.
   *  The Tseitin transformation results in an _equisatisfiable_
   *  CNF-formula (it generates auxiliary variables)
   *  but runs with linear complexity.
   */
  trait TseitinCNF extends PropositionalLogic {
    type Clause = CNFBuilder#Clause

    def eqFreePropToSolvable(p: Prop): Solvable = {
      type Cache = Map[Prop, Lit]

      val cache = mutable.Map[Prop, Lit]()

      val cnf = new CNFBuilder

      def convertWithoutCache(p: Prop): Lit = {
        p match {
          case And(fv) =>
            and(fv.map(convertWithCache))
          case Or(fv) =>
            or(fv.map(convertWithCache))
          case Not(a) =>
            not(convertWithCache(a))
          case _: Sym =>
            val l = cnf.newLiteral()
            println(s"created $l for $p")
            l
          case True =>
            cnf.constTrue
          case False =>
            cnf.constFalse
          case _: Eq =>
            debug.patmat("Forgot to call propToSolvable()?")
            throw new MatchError(p)
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

      def and(bv: mutable.LinkedHashSet[Lit]): Lit = {
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
          new_bv.map(op => addClauseProcessed(op, -o))
          addClauseProcessed((new_bv.map(op => -op) + o).toSeq: _*)
          o
        }
      }

      def or(bv: mutable.LinkedHashSet[Lit]): Lit = {
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
          new_bv.map(op => addClauseProcessed(-op, o))
          addClauseProcessed((new_bv + (-o)).toSeq: _*)
          o
        }
      }

      // no need for auxiliary variable
      def not(a: Lit): Lit = -a

      def toLiteral(f: Prop): Option[Lit] = f match {
        case Not(a) =>
          toLiteral(a).map(lit => -lit)
        case sym: Sym =>
//          Some(convertWithCache(f)) // go via cache in order to get single literal for variable

          val l: Lit = Lit(sym.id)
          cache += (sym -> l)
          Some(l) // keep variable number to get compatible ordering
        case True   =>
          Some(cnf.constTrue)
        case False  =>
          Some(cnf.constFalse)
        case _      =>
          None
      }

      object ToDisjunction {
        def unapply(f: Prop): Option[Clause] = f match {
          case Or(fv) =>
            val a: Option[Clause] = fv.foldLeft(Option(Set[Lit]())) {
              case (Some(clause), p) =>
                toLiteral(p).map(clause + _)
              case (_, _)            =>
                None
            }
            a
          case p      =>
            toLiteral(p).map(Set(_))
        }
      }

      /**
       * Checks if propositional formula is already in CNF
       */
      object ToCnf {
        def unapply(f: Prop): Option[mutable.ArrayBuffer[Clause]] = f match {
          case And(fv) =>
            fv.foldLeft(Option(mutable.ArrayBuffer[Clause]())) {
              case (Some(cnf), ToDisjunction(clause)) =>
                Some(cnf += clause)
              case (_, _)                             =>
                None
            }
//          case True    =>
//            Some(cnf.constTrue)
//          case False   =>
//            Some(cnf.constFalse)
          case p       =>
            ToDisjunction.unapply(p).map(mutable.ArrayBuffer[Clause](_))
        }
      }

      val simplified: Prop = simplify(p)
      simplified match {
        case ToCnf(clauses) =>
//          println("already in CNF")
          // already in CNF, just add clauses
          clauses.foreach(clause => cnf.addClauseRaw(clause))
        case p              =>
//          println("convert to CNF")
          // add intermediate variable since we want the formula to be SAT!
          cnf.addClauseProcessed(convertWithCache(p))
      }

      // all variables are guaranteed to be in cache
      // (doesn't mean they will appear in the resulting formula)
      val symForVar: Map[Int, Sym] = cache.collect {
        case (sym: Sym, lit) => lit.variable -> sym
      }(collection.breakOut) // breakOut in order to obtain immutable Map

      Solvable(cnf, symForVar)
    }

  }

  // simple wrapper around a SAT solver
  trait Solver extends TseitinCNF {

    // a clause is a disjunction of distinct literals
    def clause(l: Lit*): Clause = (
      if (l.lengthCompare(1) <= 0) {
        l.toSet // SI-8531 Avoid LinkedHashSet's bulk for 0 and 1 element clauses
      } else {
        // neg/t7020.scala changes output 1% of the time, the non-determinism is quelled with this linked set
        mutable.LinkedHashSet(l: _*)
      }
      )

    def cnfString(f: Array[Clause]): String = {
      val lits: Array[List[String]] = f map (_.map(_.toString).toList)
      val xss: List[List[String]] = lits toList
      val a: String = alignAcrossRows(xss, "\\/", " /\\\n")
      a
    }

    // adapted from http://lara.epfl.ch/w/sav10:simple_sat_solver (original by Hossein Hojjat)
    val EmptyModel = collection.immutable.SortedMap.empty[Sym, Boolean]
    val NoModel: Model = null

    // this model contains the auxiliary variables as well
    type TseitinModel = collection.immutable.SortedSet[Lit]
    val EmptyTseitinModel = collection.immutable.SortedSet.empty[Lit]
    val NoTseitinModel: TseitinModel = null

    def findModelFor(solvable: Solvable): Model = {
      import solvable._
      debug.patmat(s"searching for one model for:\n${cnf.dimacs}")

//      val start = if (Statistics.canEnable) Statistics.startTimer(patmatAnaSAT) else null

      val solver = SolverFactory.newDefault()
//      solver.setTimeoutMs(timeout)

      val satisfiableWithModel: Model = try {
        solver.addAllClauses(clausesForCnf(cnf))

        if (solver.isSatisfiable) {
          extractModel(solver, symForVar)
        } else {
          NoModel
        }
      } catch {
        case _: ContradictionException =>
          // TODO not sure if it's ok for this to happen since we have constant propagation
          NoModel
        case _: TimeoutException       =>
          throw AnalysisBudget.exceeded
      }

//      if (Statistics.canEnable) Statistics.stopTimer(patmatAnaSAT, start)

      println("onemodel")
      printModels(List(satisfiableWithModel))

      satisfiableWithModel
    }

    // returns all solutions, if any
    def findAllModelsFor(solvable: Solvable): List[Model] = {
      import solvable._
      debug.patmat(s"searching for all models for:\n${cnf.dimacs}")

      val solver: ModelIterator = new ModelIterator(SolverFactory.newDefault())
//      solver.setTimeoutMs(timeout)

      import scala.reflect.internal.util.Statistics

//      val start = if (Statistics.canEnable) Statistics.startTimer(patmatAnaSAT) else null
      val models = try {
        @tailrec
        def allModels(acc: List[Model] = Nil): List[Model] = if (solver.isSatisfiable()) {
          val valuation = extractModel(solver, symForVar)
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
          throw AnalysisBudget.exceeded
      }

//      if (Statistics.canEnable) Statistics.stopTimer(patmatAnaSAT, start)

      println("problem")
      println(cnfString(solvable.cnf.clauses))
      println("allmodels")
      printModels(models)

      models
    }

    def printModels(models: List[Model]) {
      val groupedByKey = models.groupBy {
        model => model.keySet
      }.mapValues {
        models =>
          models.sortWith {
            case (a, b) =>
            val keys = a.keys
            val decider = keys.dropWhile(key => a(key) == b(key))
            decider.headOption.map(key => a(key) < b(key)).getOrElse(false)
          }
      }

      val sortedByKeys: Seq[(SortedSet[Sym], List[Model])] = groupedByKey.toSeq.sortBy {
        case (syms, models) => syms.map(_.id).toIterable
      }

      for {
        (keys, models) <- sortedByKeys
        model <- models
      } {
        println(model)
      }
    }

    private def clausesForCnf(cnf: CNFBuilder): IVec[IVecInt] = {
      val clauses: Array[IVecInt] = cnf.clauses.map(clause => new VecInt(clause.map(_.dimacs).toArray))
      val cl = new Vec(clauses)
      println(cl)
      cl
    }

    private def extractModel(solver: ISolver, symForVar: Map[Int, Sym]): Model = {
      val model = solver.model()

      val model0 = model.toSet
      require(model.length == model0.size, "literal lost")

      object PolarityForVar {
        def unapply(v: Int): Option[Boolean] = {
          if (model0.contains(v)) {
            Some(true)
          } else if (model0.contains(-v)) {
            Some(false)
          } else {
            // literal has no influence on formula
            sys.error(s"Literal not found ${v} (should assume nondet)")
            // (if uncommented this error causes the regression tests to fail)
            // TODO: not sure if just omitting is causing other problems
            None
          }
        }
      }

      // don't extract intermediate literals
      collection.immutable.SortedMap(symForVar.toSeq.collect {
        case (PolarityForVar(polarity), sym) => sym -> polarity
      }: _*)
    }
  }
}
