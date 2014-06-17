/* NSC -- new Scala compiler
 *
 * Copyright 2011-2013 LAMP/EPFL
 * @author Adriaan Moors
 */

package scala.tools.nsc.transform.patmat

import scala.collection.mutable
import scala.reflect.internal.util.Statistics
import scala.language.postfixOps
import scala.reflect.internal.util.Collections._

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
    def Lit(pos: Boolean): Lit
    def negateLit(l: Lit): Lit

    def andFormula(a: Formula, b: Formula): Formula = a ++ b
    def simplifyFormula(a: Formula): Formula = a.distinct

    private def merge(a: Clause, b: Clause) = a ++ b

    // throws an AnalysisBudget.Exception when the prop results in a CNF that's too big
    // TODO: be smarter/more efficient about this (http://lara.epfl.ch/w/sav09:tseitin_s_encoding)
    def eqFreePropToSolvable(p: Prop): Formula = {

      val TrueF = formula()
      val FalseF = formula(clause())
      def lit(s: Sym) = formula(clause(Lit(s)))
      def negLit(s: Sym) = formula(clause(Lit(s, pos = false)))

      def conjunctiveNormalForm(p: Prop): Formula = {

        val formula = formulaBuilder

        def convert(p: Prop): Lit = {
          p match {
            case And(fv) =>
              and(fv.map(convert))
            case Or(fv)  =>
              or(fv.map(convert))
            case Not(a)  =>
              negateLit(convert(a))
            case s: Sym  =>
              Lit(s)
            case True    =>
              debug.patmat("Forgot to call simplify?")
              throw new MatchError(p)
            case False =>
              debug.patmat("Forgot to call simplify?")
              throw new MatchError(p)
            case _: Eq   =>
              debug.patmat("Forgot to call propToSolvable()?")
              throw new MatchError(p)
          }
        }

        def and(ops: mutable.LinkedHashSet[Lit]): Lit = {
          // op1*op2*...*opx <==> (op1 + o')(op2 + o')... (opx + o')(op1' + op2' +... + opx' + o)
          val o = Lit(true) // auxiliary Tseitin variable
          formula += ops + negateLit(o)
          ops.foreach(op => formula += clause(negateLit(op), o))
          o
        }

        def or(ops: mutable.LinkedHashSet[Lit]): Lit = {
          // op1+op2+...+opx <==> (op1' + o)(op2' + o)... (opx' + o)(op1 + op2 +... + opx + o')
          val o = Lit(true) // auxiliary Tseitin variable
          formula += ops.map(negateLit) + o
          ops.foreach(op => formula += clause(op, negateLit(o)))
          o
        }

        formula += clause(convert(p))
        formula
      }

      object IsDisjunction {
        def unapply(p: Prop): Option[Clause] = p match {
          case Or(fv) =>
            fv.foldLeft(Option(collection.Set[Lit]())) {
              case (Some(clause), sym: Sym) =>
                Some(clause + Lit(sym))
              case (Some(clause), Not(sym: Sym)) =>
                Some(clause + Lit(sym, false))
              case (_, _)                   =>
                None
            }
          case sym: Sym =>
            Some(collection.Set(Lit(sym)))
          case Not(sym: Sym) =>
            Some(collection.Set(Lit(sym, false)))
          case _        =>
            None
        }
      }

      /**
       * Checks if propositional formula is already in CNF
       */
      object IsCnf {
        def unapply(f: Prop): Option[ArrayBuffer[Clause]] = f match {
          case And(fv) =>
            fv.foldLeft(Option(formulaBuilder)) {
              case (Some(cnf), IsDisjunction(clause)) =>
                Some(cnf += clause)
              case (_, _)                             =>
                None
            }
          case True    =>
            Some(TrueF)
          case False   =>
            Some(FalseF)
          case p       =>
            IsDisjunction.unapply(p).map(formulaBuilder += _)
        }
      }

      val start = if (Statistics.canEnable) Statistics.startTimer(patmatCNF) else null
      val simplified = simplify(p)
      val res = simplified match {
        case IsCnf(clauses) =>
          // already in CNF, just add clauses
          clauses
        case p              =>
          // expand formula into CNF
          conjunctiveNormalForm(p)
      }

      if (Statistics.canEnable) Statistics.stopTimer(patmatCNF, start)

      //
      if (Statistics.canEnable) patmatCNFSizes(res.size).value += 1

//      debug.patmat("cnf for\n"+ p +"\nis:\n"+cnfString(res))
      res
    }
  }

  // simple solver using DPLL
  trait Solver extends CNF {
    // a literal is a (possibly negated) variable
    def Lit(sym: Sym, pos: Boolean = true) = new Lit(Some(sym), pos, -1)
    var tseitinLits = -1
    def Lit(pos: Boolean) = {
      tseitinLits += 1
      new Lit(None, pos, tseitinLits)
    }
    // TODO: kill case class
    case class Lit(sym: Option[Sym], pos: Boolean, number: Int) {
      override def toString = {
        val symOpt = sym.fold(s"TseitinVar$number")(_.toString)
        if (!pos) "-"+ symOpt else symOpt
      }

      def unary_- = Lit(sym, !pos, number)
    }

    def negateLit(l: Lit): Lit = -l

    def cnfString(f: Formula) = alignAcrossRows(f map (_.toList) toList, "\\/", " /\\\n")

    // adapted from http://lara.epfl.ch/w/sav10:simple_sat_solver (original by Hossein Hojjat)
    val EmptyModel = collection.immutable.SortedMap.empty[Sym, Boolean]
    val NoModel: Model = null

    // returns all solutions, if any (TODO: better infinite recursion backstop -- detect fixpoint??)
    def findAllModelsFor(f: Formula): List[Model] = {
      val vars: Set[Sym] = f.flatMap(_ collect {case Lit(Some(sym), _) => sym}).toSet
      // debug.patmat("vars "+ vars)
      // the negation of a model -(S1=True/False /\ ... /\ SN=True/False) = clause(S1=False/True, ...., SN=False/True)
      def negateModel(m: Model) = clause(m.toSeq.map{ case (sym, pos) => Lit(sym, !pos) } : _*)

      def findAllModels(f: Formula, models: List[Model], recursionDepthAllowed: Int = 10): List[Model]=
        if (recursionDepthAllowed == 0) models
        else {
          debug.patmat("find all models for\n"+ cnfString(f))
          val model = findModelFor(f)
          // if we found a solution, conjunct the formula with the model's negation and recurse
          if (model ne NoModel) {
            val unassigned = (vars -- model.keySet).toList
            debug.patmat("unassigned "+ unassigned +" in "+ model)
            def force(lit: Lit) = {
              val model = withLit(findModelFor(dropUnit(f, lit)), lit)
              if (model ne NoModel) List(model)
              else Nil
            }
            val forced = unassigned flatMap { s =>
              force(Lit(s, pos = true)) ++ force(Lit(s, pos = false))
            }
            debug.patmat("forced "+ forced)
            val negated = negateModel(model)
            findAllModels(f :+ negated, model :: (forced ++ models), recursionDepthAllowed - 1)
          }
          else models
        }

      findAllModels(f, Nil)
    }

    private def withLit(res: Model, l: Lit): Model =
      if (res eq NoModel)
        NoModel
      else l.sym match {
        case Some(sym) => res + (sym -> l.pos)
        case None      => NoModel
      }

    private def dropUnit(f: Formula, unitLit: Lit): Formula = {
      val negated = -unitLit
      // drop entire clauses that are trivially true
      // (i.e., disjunctions that contain the literal we're making true in the returned model),
      // and simplify clauses by dropping the negation of the literal we're making true
      // (since False \/ X == X)
      val dropped = formulaBuilderSized(f.size)
      for {
        clause <- f
        if !(clause contains unitLit)
      } dropped += (clause - negated)
      dropped
    }

    def findModelFor(f: Formula): Model = {
      @inline def orElse(a: Model, b: => Model) = if (a ne NoModel) a else b

      debug.patmat("DPLL\n"+ cnfString(f))

      val start = if (Statistics.canEnable) Statistics.startTimer(patmatAnaDPLL) else null

      val satisfiableWithModel: Model =
        if (f isEmpty) EmptyModel
        else if(f exists (_.isEmpty)) NoModel
        else f.find(_.size == 1) match {
          case Some(unitClause) =>
            val unitLit = unitClause.head
            // debug.patmat("unit: "+ unitLit)
            withLit(findModelFor(dropUnit(f, unitLit)), unitLit)
          case _ =>
            // partition symbols according to whether they appear in positive and/or negative literals
            // SI-7020 Linked- for deterministic counter examples.
            val pos = new mutable.LinkedHashSet[Lit]()
            val neg = new mutable.LinkedHashSet[Lit]()
            mforeach(f)(lit => if (lit.pos) pos += lit else neg += -lit)

            // appearing in both positive and negative
            val impures: mutable.LinkedHashSet[Lit] = pos intersect neg
            // appearing only in either positive/negative positions
            val pures: mutable.LinkedHashSet[Lit] = (pos ++ neg) -- impures

            if (pures nonEmpty) {
              // turn it back into a positive literal
              val pureLit = pures.head.copy(pos = true)
              // debug.patmat("pure: "+ pureLit +" pures: "+ pures +" impures: "+ impures)
              val simplified = f.filterNot(_.contains(pureLit))
              withLit(findModelFor(simplified), pureLit)
            } else {
              val split = f.head.head
              // debug.patmat("split: "+ split)
              orElse(findModelFor(f :+ clause(split)), findModelFor(f :+ clause(-split)))
            }
        }

      if (Statistics.canEnable) Statistics.stopTimer(patmatAnaDPLL, start)
      satisfiableWithModel
    }
  }
}
