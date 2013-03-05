/* NSC -- new Scala compiler
 *
 * Copyright 2011-2013 LAMP/EPFL
 * @author Adriaan Moors
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

// naive CNF translation and simple DPLL solver
trait Sat4JSolving extends Logic {
  import PatternMatchingStats._

// derived from http://websvn.ow2.org/listing.php?repname=sat4j&path=%2Fmaven%2Ftrunk%2Forg.sat4j.scala%2Fsrc%2Fmain%2Fscala%2Forg%2Fsat4j%2Fscala%2F
// no license was specified in this subdirectory, so EPL (governing the rest of the repo) was assumed
// TOOD: contact authors


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
  

  trait TseitinCNF extends PropositionalLogic {
    import scala.collection.mutable.ArrayBuffer
    type FormulaBuilder = ArrayBuffer[Clause]
    def formulaBuilder  = ArrayBuffer[Clause]()
    def formulaBuilderSized(init: Int)  = new ArrayBuffer[Clause](init)
    def addFormula(buff: FormulaBuilder, f: Formula): Unit = buff ++= f
    def toFormula(buff: FormulaBuilder): Formula = buff

    // CNF: a formula is a conjunction of clauses
    type Formula = FormulaBuilder
    def formula(c: Clause*): Formula = ArrayBuffer(c: _*)

    type Clause = VecInt
    // a clause is a disjunction of distinct literals
    def clause(l: Lit*): Clause = {
      val clause = new VecInt()
      l foreach clause.push
      clause
    }

    def andFormula(a: Formula, b: Formula): Formula = a ++ b
    def simplifyFormula(a: Formula): Formula = a.distinct

    private def merge(a: Clause, b: Clause) = clause((a.toArray ++ b.toArray) : _*)

    type Lit = Int
    // a literal is a (possibly negated) variable
    private[this] val lits = mutable.ArrayBuffer[Sym]()
    def Lit(sym: Sym, pos: Boolean = true) = {
      val idx = lits.indexOf(sym) match {
        case -1 =>
          lits += sym
          lits.size - 1
        case i => i
      }
      if (pos) idx + 1
      else -(idx + 1)
    }
    def litToSym(lit: Lit): Sym = lits(lit.abs - 1)

//    case class Formula(vars: Array[Array[Int]], model: HashMap[Prop, Int])
    
//    def cnfString(f: Formula) = alignAcrossRows(f map (_.toList) toList, "\\/", " /\\\n")

    def eqFreePropToSolvable(p: Prop): Formula  = {
      _createdVars = List()
      _varId = 0
      encode(simplifyCnf(cnf.toCnfList))
    }

    def encode(cnf: List[List[Prop]]): (List[List[Int]], Map[Prop, Int]) = {
      encodeCnf0(cnf, Map[Prop, Int]())
    }

    def encodeCnf0(cnf: List[List[Prop]], m: Map[Prop, Int]): (List[List[Int]], Map[Prop, Int]) = cnf match {
      case Nil => (List(), m)
      case h :: t =>
        val p = encodeClause0(h, m)
        p match {
          case (Nil, _) => (List(List()), m)
          case (l, mUpdated) =>
            val (newVars, newModel) = encodeCnf0(t, mUpdated)
            (l :: newVars, newModel)
        }
    }


    def inv(x: Int): Int = -x

    def encodeClause0(c: List[Prop], m: Map[Prop, Int]): (List[Int], Map[Prop, Int]) = c match {
      case Nil                              => (List(), m)
      case (s: AnonymousVariable) :: q      => encodeClause1(s, q, m, x => x)
      case (s: Lit) :: q               => encodeClause1(s, q, m, x => x)
      case (Not(s: AnonymousVariable)) :: q => encodeClause1(s, q, m, inv)
      case (Not(s: Lit)) :: q          => encodeClause1(s, q, m, inv)

      case _                                => throw new Exception("There is something that is not a litteral in the clause " + PrettyPrint(List(c)))
    }

    def encodeClause1(c: Prop, q: List[Prop], m: Map[Prop, Int], f: Int => Int): (List[Int], Map[Prop, Int]) = m.get(c) match {
      case Some(i) => {
        val p = encodeClause0(q, m)
        (f(i) :: p._1, p._2)
      }
      case None => {
        val n = m.size + 1
        val p = encodeClause0(q, m.updated(c, n))
        (f(n) :: p._1, p._2)
      }
    }
    
    
    /** Returns true iff the given expression is already in conjunctive normal form. */
    def isAlreadyInCnf(f: Prop): (Boolean, Option[List[List[Prop]]]) = f match {
      case And(b1, b2) => {
        val (r1, l1) = isAlreadyInCnf(b1)
        if (r1) {
          val (r2, l2) = isAlreadyInCnf(b2)
          if (r2) (true, Some(l1.get ++ l2.get))
          else (false, None)
        } else (false, None)
      }
      case Or(b1, b2) => isDisjunction(f)
      case _          => isLiteral(f)
    }

    def isDisjunction(f: Prop): (Boolean, Option[List[List[Prop]]]) = f match {
      case Or(b1, b2) => {
        val (r1, l1) = isDisjunction(b1)
        if (r1) {
          val (r2, l2) = isDisjunction(b2)
          if (r2) (true, Some(List(l1.get(0) ++ l2.get(0))))
          else (false, None)
        } else (false, None)
      }
      case _ => isLiteral(f)
    }

    def isLiteral(f: Prop): (Boolean, Option[List[List[Prop]]]) = f match {
      case True          => (true, Some(List(List(True))))
      case False         => (true, Some(List(List(False))))
      case Lit(_)      => (true, Some(List(List(f))))
      case Not(Lit(_)) => (true, Some(List(List(f))))
      case _             => (false, None)
    }

    def tseitinListSimple(b: Prop, l: List[List[Prop]]): (Prop, List[List[Prop]]) = {
      b match {

        case True               => (True, List())
        case Not(False)         => (True, List())

        case False              => (False, List())
        case Not(True)          => (False, List())

        case Lit(s)           => (Lit(s), List())


        case Not(b1) => {
          val v = newVar
          val t1 = tseitinListSimple(b1, List())
          (v, List(~t1._1, ~v) :: List(t1._1, v) :: t1._2)
        }

        case And(b1, b2) => {
          val v = newVar
          val t1 = tseitinListSimple(b1, List())
          val t2 = tseitinListSimple(b2, List())
          (v, List(~t1._1, ~t2._1, v) :: List(t1._1, ~v) :: List(t2._1, ~v) :: t1._2 ++ t2._2)

        }

        case Or(b1, b2) => {
          val v = newVar
          val t1 = tseitinListSimple(b1, List())
          val t2 = tseitinListSimple(b2, List())
          (v, List(t1._1, t2._1, ~v) :: List(~t1._1, v) :: List(~t2._1, v) :: t1._2 ++ t2._2)
        }

      }
    }

    def simplifyClause(c: List[Prop]): List[Prop] = c match {
      case Nil             => List()
      case True :: t       => List(True)
      case Not(False) :: t => List(True)
      case False :: t      => simplifyClause(t)
      case Not(True) :: t  => simplifyClause(t)
      case h :: t          => h :: simplifyClause(t)
    }

    def simplifyCnf(l: List[List[Prop]]): List[List[Prop]] = l match {
      case Nil => List()
      case h :: t => {
        val s = simplifyClause(h)
        s match {
          case List()     => List(List())
          case List(True) => simplifyCnf(t)
          case _          => s :: simplifyCnf(t)
        }
      }
    }



    /** Anonymous logical proposition. */
    case class AnonymousVariable extends Prop {
      private val id = nextVarId
      override def toString = "_nv#" + id
      override def equals(o: Any) = o match {
        case x: AnonymousVariable => id == x.id
        case _                    => false
      }
      override def hashCode() = id
    }

    private var _varId = 0
    private def nextVarId = { _varId += 1; _varId };
    private var _createdVars = List[AnonymousVariable]()

    /** create new propositional variables for translation into CNF */
    private def newVar = if (_cachedVar != null) { val tmp = _cachedVar; _cachedVar = null; tmp } else uncachedNewVar

    def uncachedNewVar = {
      val v = new AnonymousVariable
      _createdVars = v :: _createdVars
      v
    }

    private def nextAnonymousVar = if (_cachedVar == null) { _cachedVar = uncachedNewVar; _cachedVar } else _cachedVar;

    var _cachedVar = uncachedNewVar

    /** n-ary conjunction. */
    def and(l: Prop*): Prop = and(l.toList)

    /** n-ary conjunction. */
    def and(l: List[Prop]): Prop = l match {
      case Nil      => True
      case b :: Nil => b
      case b :: t   => l.reduceLeft { (b1, b2) => And(b1, b2) }
    }

    /** n-ary disjunction. */
    def or(l: Prop*): Prop = or(l.toList)

    /** n-ary disjunction. */
    def or(l: List[Prop]): Prop = l match {
      case Nil      => False
      case b :: Nil => b
      case b :: t   => l.reduceLeft { (b1, b2) => Or(b1, b2) }
    }
  }

  class Solver extends TseitinCNF {

    def isSat[U](problem: Formula): (Boolean, Option[Map[U, Boolean]]) = {
      try {
        val res = problem.solve
        res match {
          case Satisfiable => {
            val listeBoolExp = problem.model.toList map { x => if (x > 0) (litToSym(x) -> true) else (litToSym(-x) -> false) }
            val mapIdentBool = listeBoolExp filter (x => x match {
              case (s: AnonymousVariable, _) => false
              case (Lit(_), _)             => true
              case _                         => false
            })
            val mapUBool = mapIdentBool map (z => z match {
              case (Lit(s), b) => (s, b)
              case _                => throw new IllegalStateException
            })
            (true, Some(mapUBool.toMap))
          }
          case Unsatisfiable => (false, None)
          case _             => throw new IllegalStateException("Got a time out")
        }
      } catch {
        case e: ContradictionException => (false, None)
      }
    }

    def isValid[U](f: Prop): (Boolean, Option[Map[U, Boolean]]) = {
      val (b, m) = isSat[U](~f)
      (!b, m)
    }
    
    // adapted from http://lara.epfl.ch/w/sav10:simple_sat_solver (original by Hossein Hojjat)
    val EmptyModel = Map.empty[Sym, Boolean]
    val NoModel: Model = null

    // returns all solutions, if any (TODO: better infinite recursion backstop -- detect fixpoint??)
    def findAllModelsFor(f: Formula): List[Model] = {
      val vars: Set[Sym] = f.flatMap(_ collect { case l: Lit => l.sym }).toSet
      // debug.patmat("vars "+ vars)
      // the negation of a model -(S1=True/False /\ ... /\ SN=True/False) = clause(S1=False/True, ...., SN=False/True)
      def negateModel(m: Model) = clause(m.toSeq.map{ case (sym, pos) => Lit(sym, !pos) }: _*)

      def findAllModels(f: Formula, models: List[Model], recursionDepthAllowed: Int = 10): List[Model] =
        if (recursionDepthAllowed == 0) models
        else {
          debug.patmat("find all models for\n" + cnfString(f))
          val model = findModelFor(f)
          // if we found a solution, conjunct the formula with the model's negation and recurse
          if (model ne NoModel) {
            val unassigned = (vars -- model.keySet).toList
            debug.patmat("unassigned " + unassigned + " in " + model)
            def force(lit: Lit) = {
              val model = withLit(findModelFor(dropUnit(f, lit)), lit)
              if (model ne NoModel) List(model)
              else Nil
            }
            val forced = unassigned flatMap { s =>
              force(Lit(s, true)) ++ force(Lit(s, false))
            }
            debug.patmat("forced " + forced)
            val negated = negateModel(model)
            findAllModels(f :+ negated, model :: (forced ++ models), recursionDepthAllowed - 1)
          } else models
        }

      findAllModels(f, Nil)
    }

    def findModelFor(f: Formula): Model
    
  }
  
  //  /** A pretty printer for logic syntax trees. */
  //  object PrettyPrint {
  //    def apply(e: Exp): String = e match {
  //      case True => "True"
  //      case False => "False"
  //      case Not(True) => "~True"
  //      case Not(False) => "~False"
  //      case v: AnonymousVariable => v.toString
  //      case Not(v: AnonymousVariable) => "~" + v.toString
  //      case Ident(s) => s.toString
  //      case IndexedIdent(s, is) => s.toString + is.mkString("(", ",", ")")
  //      case Not(Ident(s)) => "~" + s
  //      case Not(IndexedIdent(s, is)) => "~" + s.toString + is.mkString("(", ",", ")")
  //      case Not(b) => "~(" + apply(b) + ")"
  //      case And(b1, b2) => "(" + apply(b1) + " & " + apply(b2) + ")"
  //      case Or(b1, b2) => "(" + apply(b1) + " | " + apply(b2) + ")"
  //      case Implies(b1, b2) => "(" + apply(b1) + " implies " + apply(b2) + ")"
  //      case Iff(b1, b2) => "(" + apply(b1) + " iff " + apply(b2) + ")"
  //      case CardEQ(bs, k) => "(" + bs.map(apply).mkString(" + ") + " === " + k + ")"
  //      case CardLE(bs, k) => "(" + bs.map(apply).mkString(" + ") + " <= " + k + ")"
  //      case CardLT(bs, k) => "(" + bs.map(apply).mkString(" + ") + " < " + k + ")"
  //      case CardGE(bs, k) => "(" + bs.map(apply).mkString(" + ") + " >= " + k + ")"
  //      case CardGT(bs, k) => "(" + bs.map(apply).mkString(" + ") + " > " + k + ")"
  //    }
  //
  //    def apply(cnfList: List[List[Prop]]): String =
  //      cnfList match {
  //        case Nil => "";
  //        case c :: t => {
  //          val line =
  //            for (l <- c) yield apply(l)
  //          "\n" + (line mkString " ") + apply(t)
  //        }
  //      }
  //  }

  //  /** Implicit conversion from string to logical identifier */
  //  implicit def identFromString(s: String): Ident[String] = Ident(s)
  //
  //  /** Implicit conversion from string to logical identifier */
  //  implicit def identFromSymbol(i: Symbol): Ident[Symbol] = Ident(i)
  //
  //  /** Convert any Scala object into a propositional variable */
  //  def toProp[U](u: U): Ident[U] = Ident(u)

}

