/* NSC -- new Scala compiler
 *
 * Copyright 2011-2013 LAMP/EPFL
 * @author Adriaan Moors
 */

package scala.tools.nsc.transform.patmat

import scala.collection.immutable.SortedSet
import scala.collection.mutable
import scala.reflect.internal.util.Statistics
import scala.language.postfixOps
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

// naive CNF translation and simple DPLL solver
trait Solving extends Logic {
  import PatternMatchingStats._
  trait CNF extends PropositionalLogic {
    import scala.collection.mutable.ArrayBuffer
    type FormulaBuilder = ArrayBuffer[Clause]
    def formulaBuilder  = ArrayBuffer[Clause]()
    def formulaBuilderSized(init: Int)  = new ArrayBuffer[Clause](init)
    def addFormula(buff: FormulaBuilder, f: Formula): Unit = buff ++= f
    def toFormula(buff: FormulaBuilder): Formula = buff

    // CNF: a formula is a conjunction of clauses
    type Formula = FormulaBuilder
    def formula(c: Clause*): Formula = ArrayBuffer(c: _*)

    type Clause  = collection.Set[Lit]
    // a clause is a disjunction of distinct literals
    def clause(l: Lit*): Clause = (
      if (l.lengthCompare(1) <= 0) {
        l.toSet // SI-8531 Avoid LinkedHashSet's bulk for 0 and 1 element clauses
      } else {
        // neg/t7020.scala changes output 1% of the time, the non-determinism is quelled with this linked set
        mutable.LinkedHashSet(l: _*)
      }
    )

    type Lit
    def Lit(sym: Sym, pos: Boolean = true): Lit

    def andFormula(a: Formula, b: Formula): Formula = a ++ b
    def simplifyFormula(a: Formula): Formula = a.distinct

    private def merge(a: Clause, b: Clause) = a ++ b

    // throws an AnalysisBudget.Exception when the prop results in a CNF that's too big
    // TODO: be smarter/more efficient about this (http://lara.epfl.ch/w/sav09:tseitin_s_encoding)
    def eqFreePropToSolvable(p: Prop): Formula = {

      println("eqFreePropToSolvable")
      println(p)

      def negationNormalFormNot(p: Prop, budget: Int): Prop =
        if (budget <= 0) throw AnalysisBudget.exceeded
        else p match {
          case And(a, b) =>  Or(negationNormalFormNot(a, budget - 1), negationNormalFormNot(b, budget - 1))
          case Or(a, b)  => And(negationNormalFormNot(a, budget - 1), negationNormalFormNot(b, budget - 1))
          case Not(p)    => negationNormalForm(p, budget - 1)
          case True      => False
          case False     => True
          case s: Sym    => Not(s)
        }

      def negationNormalForm(p: Prop, budget: Int = AnalysisBudget.max): Prop =
        if (budget <= 0) throw AnalysisBudget.exceeded
        else p match {
          case And(a, b)      => And(negationNormalForm(a, budget - 1), negationNormalForm(b, budget - 1))
          case Or(a, b)       =>  Or(negationNormalForm(a, budget - 1), negationNormalForm(b, budget - 1))
          case Not(negated)   => negationNormalFormNot(negated, budget - 1)
          case True
             | False
             | (_ : Sym)      => p
        }

      val TrueF          = formula()
      val FalseF         = formula(clause())
      def lit(s: Sym)    = formula(clause(Lit(s)))
      def negLit(s: Sym) = formula(clause(Lit(s, pos = false)))

      def conjunctiveNormalForm(p: Prop, budget: Int = AnalysisBudget.max): Formula = {
        def distribute(a: Formula, b: Formula, budget: Int): Formula =
          if (budget <= 0) throw AnalysisBudget.exceeded
          else
            (a, b) match {
              // true \/ _ = true
              // _ \/ true = true
              case (trueA, trueB) if trueA.size == 0 || trueB.size == 0 => TrueF
              // lit \/ lit
              case (a, b) if a.size == 1 && b.size == 1 => formula(merge(a(0), b(0)))
              // (c1 /\ ... /\ cn) \/ d = ((c1 \/ d) /\ ... /\ (cn \/ d))
              // d \/ (c1 /\ ... /\ cn) = ((d \/ c1) /\ ... /\ (d \/ cn))
              case (cs, ds) =>
                val (big, small) = if (cs.size > ds.size) (cs, ds) else (ds, cs)
                big flatMap (c => distribute(formula(c), small, budget - (big.size*small.size)))
            }

        if (budget <= 0) throw AnalysisBudget.exceeded

        p match {
          case True        => TrueF
          case False       => FalseF
          case s: Sym      => lit(s)
          case Not(s: Sym) => negLit(s)
          case And(a, b)   =>
            val cnfA = conjunctiveNormalForm(a, budget - 1)
            val cnfB = conjunctiveNormalForm(b, budget - cnfA.size)
            cnfA ++ cnfB
          case Or(a, b)    =>
            val cnfA = conjunctiveNormalForm(a)
            val cnfB = conjunctiveNormalForm(b)
            distribute(cnfA, cnfB, budget - (cnfA.size + cnfB.size))
        }
      }

      val start = if (Statistics.canEnable) Statistics.startTimer(patmatCNF) else null
      val res   = conjunctiveNormalForm(negationNormalForm(p))

      if (Statistics.canEnable) Statistics.stopTimer(patmatCNF, start)

      //
      if (Statistics.canEnable) patmatCNFSizes(res.size).value += 1

//      debug.patmat("cnf for\n"+ p +"\nis:\n"+cnfString(res))
      res
    }
  }

  // simple wrapper around a SAT solver
  trait Solver extends CNF {
    // a literal is a (possibly negated) variable
    def Lit(sym: Sym, pos: Boolean = true) = new Lit(sym, pos)
    class Lit(val sym: Sym, val pos: Boolean) {
      override def toString = if (!pos) "-"+ sym.toString else sym.toString
      override def equals(o: Any) = o match {
        case o: Lit => (o.sym eq sym) && (o.pos == pos)
        case _ => false
      }
      override def hashCode = sym.hashCode + pos.hashCode

      def unary_- = Lit(sym, !pos)
    }

    def cnfString(f: Formula) = alignAcrossRows(f map (_.toList) toList, "\\/", " /\\\n")

    // adapted from http://lara.epfl.ch/w/sav10:simple_sat_solver (original by Hossein Hojjat)
    val EmptyModel = collection.immutable.SortedMap.empty[Sym, Boolean]
    val NoModel: Model = null

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

    def findModelFor(f: Formula): Model = {
//      debug.patmat(s"searching for one model for:\n${cnf.dimacs}")
      val solver = SolverFactory.newDefault()
      //      solver.setTimeoutMs(timeout)

      val symForVar: Map[Int, Sym] = (for {
        s <- f
        l <- s
      } yield {
        l.sym.id ->l.sym
      }).toMap

      val satisfiableWithModel = try {
        solver.addAllClauses(clausesForFormula(f))
        if (solver.isSatisfiable()) {
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

      println("onemodel")
      printModels(List(satisfiableWithModel))

      satisfiableWithModel
    }

    // returns all solutions, if any
    def findAllModelsFor(f: Formula): List[Model] = {
//      debug.patmat(s"searching for all models for:\n${cnf.dimacs}")

      val solver: ModelIterator = new ModelIterator(SolverFactory.newDefault())
      //      solver.setTimeoutMs(timeout)

      val symForVar: Map[Int, Sym] = (for {
        s <- f
        l <- s
      } yield {
        l.sym.id ->l.sym
      }).toMap

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

        solver.addAllClauses(clausesForFormula(f))

        allModels()
      } catch {
        case _: ContradictionException =>
          // TODO not sure if it's ok for this to happen since we have constant propagation
          Nil
        case _: TimeoutException       =>
          throw AnalysisBudget.exceeded
      }

      println("problem")
      println(cnfString(f))
      println("allmodels")
      printModels(models)

      models
    }

    //      if (Statistics.canEnable) Statistics.stopTimer(patmatAnaSAT, start)
    private def clausesForFormula(f: Formula): IVec[IVecInt] = {
      def dimacs(lit: Lit) = if(lit.pos) lit.sym.id else -lit.sym.id
      val clauses: Array[IVecInt] = f.toArray.map(clause => new VecInt(clause.map(dimacs).toArray))
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
            // sys.error(s"Literal not found ${lit} (should assume nondet)")
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
