/* NSC -- new Scala compiler
 *
 * Copyright 2011-2013 LAMP/EPFL
 * @author Adriaan Moors
 */

package scala.tools.nsc.transform.patmat

import scala.tools.nsc.symtab._
import scala.language.postfixOps
import scala.collection.mutable
import scala.reflect.internal.util.Position
import scala.reflect.internal.util.HashSet

trait ScalaLogic extends Interface with Logic with Equality with TreeAndTypeAnalysis {
  trait TreesAndTypesLogic extends EquationalLogic with CheckableTreeAndTypeAnalysis {
    import global.{Type, Tree}

    // resets hash consing -- only supposed to be called by TreeMakersToProps
    def prepareNewAnalysis(): Unit = { Var.resetUniques(); Const.resetUniques() }

    object Var {
      private var _nextId = 0
      def nextId = {_nextId += 1; _nextId}

      def resetUniques() = {_nextId = 0; uniques.clear()}
      private val uniques = new mutable.HashMap[Tree, Var]
      def apply(x: Tree): Var = uniques getOrElseUpdate(x, new Var(x, x.tpe))
      def unapply(v: Var) = Some(v.path)
    }
    class Var(val path: Tree, staticTp: Type) extends AbsVar {
      private[this] val id: Int = Var.nextId

      // private[this] var canModify: Option[Array[StackTraceElement]] = None
      private[this] def ensureCanModify() = {} //if (canModify.nonEmpty) debug.patmat("BUG!"+ this +" modified after having been observed: "+ canModify.get.mkString("\n"))

      private[this] def observed() = {} //canModify = Some(Thread.currentThread.getStackTrace)

      // don't access until all potential equalities have been registered using registerEquality
      private[this] val symForEqualsTo = new mutable.HashMap[Const, Sym]

      // when looking at the domain, we only care about types we can check at run time
      val staticTpCheckable: Type = checkableType(staticTp)

      private[this] var _mayBeNull = false
      def registerNull(): Unit = { ensureCanModify; if (NullTp <:< staticTpCheckable) _mayBeNull = true }
      def mayBeNull: Boolean = _mayBeNull

      // case None => domain is unknown,
      // case Some(List(tps: _*)) => domain is exactly tps
      // we enumerate the subtypes of the full type, as that allows us to filter out more types statically,
      // once we go to run-time checks (on Const's), convert them to checkable types
      // TODO: there seems to be bug for singleton domains (variable does not show up in model)
      lazy val domain: Option[Set[Const]] = {
        val subConsts = enumerateSubtypes(staticTp).map{ tps =>
          tps.toSet[Type].map{ tp =>
            val domainC = TypeConst(tp)
            registerEquality(domainC)
            domainC
          }
        }

        val allConsts =
          if (mayBeNull) {
            registerEquality(NullConst)
            subConsts map (_ + NullConst)
          } else
            subConsts

        observed; allConsts
      }

      // populate equalitySyms
      // don't care about the result, but want only one fresh symbol per distinct constant c
      def registerEquality(c: Const): Unit = {ensureCanModify; symForEqualsTo getOrElseUpdate(c, Sym(this, c))}

      // return the symbol that represents this variable being equal to the constant `c`, if it exists, otherwise False (for robustness)
      // (registerEquality(c) must have been called prior, either when constructing the domain or from outside)
      def propForEqualsTo(c: Const): Prop = {observed; symForEqualsTo.getOrElse(c, False)}

      // [implementation NOTE: don't access until all potential equalities have been registered using registerEquality]p
      /** the information needed to construct the boolean proposition that encods the equality proposition (V = C)
       *
       * that models a type test pattern `_: C` or constant pattern `C`, where the type test gives rise to a TypeConst C,
       * and the constant pattern yields a ValueConst C
       *
       * for exhaustivity, we really only need implication (e.g., V = 1 implies that V = 1 /\ V = Int, if both tests occur in the match,
       * and thus in this variable's equality symbols), but reachability also requires us to model things like V = 1 precluding V = "1"
       */
      lazy val implications = {
        /** when we know V = C, which other equalities must hold
         *
         * in general, equality to some type implies equality to its supertypes
         * (this multi-valued kind of equality is necessary for unreachability)
         * note that we use subtyping as a model for implication between instanceof tests
         * i.e., when S <:< T we assume x.isInstanceOf[S] implies x.isInstanceOf[T]
         * unfortunately this is not true in general (see e.g. SI-6022)
         */
        def implies(lower: Const, upper: Const): Boolean =
          // values and null
            lower == upper ||
          // type implication
            (lower != NullConst && !upper.isValue &&
             instanceOfTpImplies(if (lower.isValue) lower.wideTp else lower.tp, upper.tp))

          // if(r) debug.patmat("implies    : "+(lower, lower.tp, upper, upper.tp))
          // else  debug.patmat("NOT implies: "+(lower, upper))


        /** does V = C preclude V having value `other`?
         (1) V = null is an exclusive assignment,
         (2) V = A and V = B, for A and B value constants, are mutually exclusive unless A == B
             we err on the safe side, for example:
               - assume `val X = 1; val Y = 1`, then
                 (2: Int) match { case X => case Y =>  <falsely considered reachable>  }
               - V = 1 does not preclude V = Int, or V = Any, it could be said to preclude V = String, but we don't model that

         (3) for types we could try to do something fancy, but be conservative and just say no
         */
        def excludes(a: Const, b: Const): Boolean =
          a != b && ((a == NullConst || b == NullConst) || (a.isValue && b.isValue))

          // if(r) debug.patmat("excludes    : "+(a, a.tp, b, b.tp))
          // else  debug.patmat("NOT excludes: "+(a, b))

/*
[ HALF BAKED FANCINESS: //!equalitySyms.exists(common => implies(common.const, a) && implies(common.const, b)))
 when type tests are involved, we reason (conservatively) under a closed world assumption,
 since we are really only trying to counter the effects of the symbols that we introduce to model type tests
 we don't aim to model the whole subtyping hierarchy, simply to encode enough about subtyping to do unreachability properly

 consider the following hierarchy:

    trait A
    trait B
    trait C
    trait AB extends B with A

  // two types are mutually exclusive if there is no equality symbol whose constant implies both
  object Test extends App {
    def foo(x: Any) = x match {
      case _ : C  => println("C")
      case _ : AB => println("AB")
      case _ : (A with B) => println("AB'")
      case _ : B  => println("B")
      case _ : A  => println("A")
    }

 of course this kind of reasoning is not true in general,
 but we can safely pretend types are mutually exclusive as long as there are no counter-examples in the match we're analyzing}
*/

        val excludedPair = new mutable.HashSet[ExcludedPair]

        case class ExcludedPair(a: Const, b: Const) {
          override def equals(o: Any) = o match {
            case ExcludedPair(aa, bb) => (a == aa && b == bb) || (a == bb && b == aa)
            case _ => false
          }
          // make ExcludedPair(a, b).hashCode == ExcludedPair(b, a).hashCode
          override def hashCode = a.hashCode ^ b.hashCode
        }

        equalitySyms map { sym =>
          // if we've already excluded the pair at some point (-A \/ -B), then don't exclude the symmetric one (-B \/ -A)
          // (nor the positive implications -B \/ A, or -A \/ B, which would entail the equality axioms falsifying the whole formula)
          val todo = equalitySyms filterNot (b => (b.const == sym.const) || excludedPair(ExcludedPair(b.const, sym.const)))
          val (excluded, notExcluded) = todo partition (b => excludes(sym.const, b.const))
          val implied = notExcluded filter (b => implies(sym.const, b.const))

          debug.patmat("eq axioms for: "+ sym.const)
          debug.patmat("excluded: "+ excluded)
          debug.patmat("implied: "+ implied)

          excluded foreach { excludedSym => excludedPair += ExcludedPair(sym.const, excludedSym.const)}

          (sym, implied, excluded)
        }
      }

      // accessing after calling registerNull will result in inconsistencies
      lazy val domainSyms: Option[Set[Sym]] = domain map { _ map symForEqualsTo }

      // accessing after calling registerNull will result in inconsistencies
      // when this variable cannot be null,
      //   we add the axiom that models that the type test `(x: T)` is true if T is x's static type
      // when the variable may be null,
      //   we refine the axiom to the implication `(x != null) => (x: T)`
      lazy val symForStaticTp: Option[Sym]  = {
        val sym = symForEqualsTo.get(TypeConst(staticTpCheckable))
        if (mayBeNull) Or(propForEqualsTo(NullConst), sym)
        else sym
      }

      // don't access until all potential equalities have been registered using registerEquality
      private lazy val equalitySyms = {observed; symForEqualsTo.values.toList}

      // don't call until all equalities have been registered and registerNull has been called (if needed)
      def describe = {
        def domain_s = domain match {
          case Some(d) => d mkString (" ::= ", " | ", "// "+ symForEqualsTo.keys)
          case _       => symForEqualsTo.keys mkString (" ::= ", " | ", " | ...")
        }
        s"$this: ${staticTp}${domain_s} // = $path"
      }
      override def toString = "V"+ id
    }


    import global.{ConstantType, Constant, SingletonType, Literal, Ident, singleType}
    import global.definitions.{AnyClass, UnitClass}


    // all our variables range over types
    // a literal constant becomes ConstantType(Constant(v)) when the type allows it (roughly, anyval + string + null)
    // equality between variables: SingleType(x) (note that pattern variables cannot relate to each other -- it's always patternVar == nonPatternVar)
    object Const {
      def resetUniques() = {_nextTypeId = 0; _nextValueId = 0; uniques.clear() ; trees.clear()}

      private var _nextTypeId = 0
      def nextTypeId = {_nextTypeId += 1; _nextTypeId}

      private var _nextValueId = 0
      def nextValueId = {_nextValueId += 1; _nextValueId}

      private val uniques = new mutable.HashMap[Type, Const]
      private[TreesAndTypesLogic] def unique(tp: Type, mkFresh: => Const): Const =
        uniques.get(tp).getOrElse(
          uniques.find {case (oldTp, oldC) => oldTp =:= tp} match {
            case Some((_, c)) =>
              debug.patmat("unique const: "+ (tp, c))
              c
            case _ =>
              val fresh = mkFresh
              debug.patmat("uniqued const: "+ (tp, fresh))
              uniques(tp) = fresh
              fresh
          })

      private val trees = mutable.HashSet.empty[Tree]

      // hashconsing trees (modulo value-equality)
      private[TreesAndTypesLogic] def uniqueTpForTree(t: Tree): Type =
        // a new type for every unstable symbol -- only stable value are uniqued
        // technically, an unreachable value may change between cases
        // thus, the failure of a case that matches on a mutable value does not exclude the next case succeeding
        // (and thuuuuus, the latter case must be considered reachable)
        if (!t.symbol.isStable) t.tpe.narrow
        else trees find (a => a.correspondsStructure(t)(sameValue)) match {
          case Some(orig) =>
            debug.patmat("unique tp for tree: "+ (orig, orig.tpe))
            orig.tpe
          case _ =>
            // duplicate, don't mutate old tree (TODO: use a map tree -> type instead?)
            val treeWithNarrowedType = t.duplicate setType t.tpe.narrow
            debug.patmat("uniqued: "+ (t, t.tpe, treeWithNarrowedType.tpe))
            trees += treeWithNarrowedType
            treeWithNarrowedType.tpe
        }
    }

    sealed abstract class Const {
      def tp: Type
      def wideTp: Type

      def isAny = wideTp.typeSymbol == AnyClass
      def isValue: Boolean //= tp.isStable

      // note: use reference equality on Const since they're hash-consed (doing type equality all the time is too expensive)
      // the equals inherited from AnyRef does just this
    }

    // find most precise super-type of tp that is a class
    // we skip non-class types (singleton types, abstract types) so that we can
    // correctly compute how types relate in terms of the values they rule out
    // e.g., when we know some value must be of type T, can it still be of type S? (this is the positive formulation of what `excludes` on Const computes)
    // since we're talking values, there must have been a class involved in creating it, so rephrase our types in terms of classes
    // (At least conceptually: `true` is an instance of class `Boolean`)
    private def widenToClass(tp: Type): Type =
      if (tp.typeSymbol.isClass) tp
      else tp.baseType(tp.baseClasses.head)

    object TypeConst {
      def apply(tp: Type) = {
        if (tp =:= NullTp) NullConst
        else if (tp.isInstanceOf[SingletonType]) ValueConst.fromType(tp)
        else Const.unique(tp, new TypeConst(tp))
      }
      def unapply(c: TypeConst): Some[Type] = Some(c.tp)
    }

    // corresponds to a type test that does not imply any value-equality (well, except for outer checks, which we don't model yet)
    sealed class TypeConst(val tp: Type) extends Const {
      assert(!(tp =:= NullTp))
      /*private[this] val id: Int = */ Const.nextTypeId

      val wideTp = widenToClass(tp)
      def isValue = false
      override def toString = tp.toString //+"#"+ id
    }

    // p is a unique type or a constant value
    object ValueConst {
      def fromType(tp: Type) = {
        assert(tp.isInstanceOf[SingletonType])
        val toString = tp match {
          case ConstantType(c) => c.escapedStringValue
          case _ => tp.toString
        }
        Const.unique(tp, new ValueConst(tp, tp.widen, toString))
      }
      def apply(p: Tree) = {
        val tp = p.tpe.normalize
        if (tp =:= NullTp) NullConst
        else {
          val wideTp = widenToClass(tp)

          val narrowTp =
            if (tp.isInstanceOf[SingletonType]) tp
            else p match {
              case Literal(c) =>
                if (c.tpe.typeSymbol == UnitClass) c.tpe
                else ConstantType(c)
              case Ident(_) if p.symbol.isStable =>
                // for Idents, can encode uniqueness of symbol as uniqueness of the corresponding singleton type
                // for Selects, which are handled by the next case, the prefix of the select varies independently of the symbol (see pos/virtpatmat_unreach_select.scala)
                singleType(tp.prefix, p.symbol)
              case _ =>
                Const.uniqueTpForTree(p)
            }

          val toString =
            if (hasStableSymbol(p)) p.symbol.name.toString // tp.toString
            else p.toString //+"#"+ id

          Const.unique(narrowTp, new ValueConst(narrowTp, checkableType(wideTp), toString)) // must make wide type checkable so that it is comparable to types from TypeConst
        }
      }
    }
    sealed class ValueConst(val tp: Type, val wideTp: Type, override val toString: String) extends Const {
      // debug.patmat("VC"+(tp, wideTp, toString))
      assert(!(tp =:= NullTp)) // TODO: assert(!tp.isStable)
      /*private[this] val id: Int = */Const.nextValueId
      def isValue = true
    }


    lazy val NullTp = ConstantType(Constant(null))
    case object NullConst extends Const {
      def tp     = NullTp
      def wideTp = NullTp

      def isValue = true
      override def toString = "null"
    }
  }
}