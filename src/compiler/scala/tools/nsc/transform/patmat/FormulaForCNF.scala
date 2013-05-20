package scala.tools.nsc.transform.patmat

import scala.annotation.tailrec

sealed abstract class FormulaForCNF

object FormulaForCNF {

  final case class And(fv: Seq[FormulaForCNF]) extends FormulaForCNF {
    override def toString: String = {
      fv.mkString("(", " & ", ")")
    }
  }

  final case class Or(fv: Seq[FormulaForCNF]) extends FormulaForCNF {
    override def toString: String = {
      fv.mkString("(", " | ", ")")
    }
  }

  final case class Not(a: FormulaForCNF) extends FormulaForCNF {
    override def toString: String = s"!${a}"
  }

  final case class Var[S](sym: S) extends FormulaForCNF {
    override def toString: String = sym.toString
  }

  case object True extends FormulaForCNF {
    override def toString: String = "T"
  }

  case object False extends FormulaForCNF {
    override def toString: String = "F"
  }

  object Or {
    def apply(f1: FormulaForCNF, f2: FormulaForCNF) = new Or(Seq(f1, f2))
  }

  object And {
    def apply(f1: FormulaForCNF, f2: FormulaForCNF) = new And(Seq(f1, f2))
  }

  /**
   * Simplifies Boolean formulae according to the following rules:
   * - eliminate double negation (avoids unnecessary Tseitin variables)
   * - flatten trees of same connectives (avoids unnecessary Tseitin variables)
   * - removes constants and connectives that are in fact constant because of their operands
   * - eliminates duplicate operands
   */
  def simplify(f: FormulaForCNF): FormulaForCNF = {
    def hasImpureAtom(ops: Seq[FormulaForCNF]): Boolean = ops.combinations(2).exists {
      case Seq(a, Not(b)) if a == b => true
      case Seq(Not(a), b) if a == b => true
      case _                        => false
    }

    @tailrec
    def isAtom(f: FormulaForCNF): Boolean = f match {
      case _: Var[_] | True | False => true
      case Not(a)                   => isAtom(a)
      case _                        => false
    }

    f match {
      case And(fv)                             =>
        val ops = fv.map(simplify).distinct.filterNot(_ == True)
        if (ops.exists(_ == False)) {
          False
        } else {
          val opsFlattened = ops.flatMap {
            case And(fv) => fv
            case f       => Seq(f)
          }

          if (hasImpureAtom(opsFlattened)) {
            False
          } else {
            opsFlattened match {
              case Seq()  => True
              case Seq(f) => f
              case ops    => And(ops)
            }
          }
        }
      case Or(fv)                              =>
        val ops = fv.map(simplify).distinct.filterNot(_ == False)
        if (ops.exists(_ == True)) {
          True
        } else {
          val opsFlattened = ops.flatMap {
            case Or(fv) => fv
            case f      => Seq(f)
          }

          if (hasImpureAtom(opsFlattened)) {
            True
          } else {
            opsFlattened match {
              case Seq()  => False
              case Seq(f) => f
              case ops    => Or(ops)
            }
          }
        }
      case Not(Not(a))                         =>
        simplify(a)
      case Not(And(ops)) if ops.forall(isAtom) =>
        // use De Morgan's rule to push negation into operands
        // (might allow flattening of tree of connectives closer to root)
        simplify(Or(ops.map(Not)))
      case Not(Or(ops)) if ops.forall(isAtom)  =>
        // De Morgan
        simplify(And(ops.map(Not)))
      case p                                   => p
    }
  }
}
