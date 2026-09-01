package ch.ethz.infsec.policy

import ch.ethz.infsec.monitor.DataType
import ch.ethz.infsec.policy.GenFormula.Signature

import java.util.concurrent.atomic.AtomicInteger
import scala.annotation.tailrec
import scala.collection.immutable.ListMap


// This is explicitly not a case class, such that each instance represent a fresh variable name.
class VariableID[N](val nameHint: N, val freeID: Int = -1) extends Serializable {
  val isFree: Boolean = freeID >= 0
  val uniqueId: Int = if (isFree) freeID else - VariableID.generator.getAndIncrement()
  override def toString: String = s"$nameHint[$uniqueId]"
}

object VariableID {
  private val generator = new AtomicInteger()
}

trait VariableMapper[V, W] {
  def bound(variable: V): (W, VariableMapper[V, W])
  def map(variable: V): W
}

class VariableResolver[N](variables: Map[N, VariableID[N]]) extends VariableMapper[N, VariableID[N]] {
  override def bound(variable: N): (VariableID[N], VariableResolver[N]) = {
    val id = new VariableID[N](variable)
    (id, new VariableResolver[N](variables.updated(variable, id)))
  }

  override def map(variable: N): VariableID[N] = variables(variable)
}

class VariablePrinter(variables: Map[VariableID[String], String]) extends VariableMapper[VariableID[String], String] {
  override def bound(variable: VariableID[String]): (String, VariablePrinter) = {
    def exists(name: String): Boolean = variables.values.exists(_ == name)
    val uniqueName = if (exists(variable.nameHint))
        (1 to Int.MaxValue).view.map(i => variable.nameHint + "_" + i.toString).find(!exists(_)).get
      else
        variable.nameHint
    (uniqueName, new VariablePrinter(variables.updated(variable, uniqueName)))
  }

  override def map(variable: VariableID[String]): String = variables(variable)
}

sealed trait TypeClass {
  def supersetEq(that: Either[TypeClass, DataType]): Boolean
}

case class AnyClass() extends TypeClass {
  override def supersetEq(that: Either[TypeClass, DataType]): Boolean = true

  override def toString: String = "any"
}

case class NumericClass() extends TypeClass {
  override def supersetEq(that: Either[TypeClass, DataType]): Boolean = that match {
    case Left(NumericClass()) => true
    case Left(_) => false
    case Right(DataType.INTEGRAL) | Right(DataType.FLOAT) => true
    case Right(_) => false
  }

  override def toString: String = "num"
}

class TypeSymbol private (private var repr: Either[TypeSymbol, Either[TypeClass, DataType]]) {
  def this(classConstraint: TypeClass) = this(Right(Left(classConstraint)))
  private def this(constType: DataType) = this(Right(Right(constType)))

  def inspect: Either[TypeClass, DataType] = repr match {
    case Left(parent) => parent.inspect
    case Right(e) => e
  }

  def shortcut: TypeSymbol = repr match {
    case Left(parent) => parent.shortcut
    case _ => this
  }

  @tailrec
  private def assign(ts: TypeSymbol): Unit = repr match {
    case Left(parent) => parent.assign(ts)
    case _ => this.repr = Left(ts.shortcut)
  }

  def unify(that: TypeSymbol): TypeSymbol = (this.inspect, that.inspect) match {
    case (Left(cls), tht) if cls.supersetEq(tht) => this.assign(that); that
    case (ths, Left(cls)) if cls.supersetEq(ths) => that.assign(this); this
    case (Right(ty1), Right(ty2)) if ty1 == ty2 => this
    case _ => throw new Exception(s"Type error: cannot unify ${this} and ${that}")
  }

  def enforceNumeric(): TypeSymbol = unify(new TypeSymbol(NumericClass()))

  override def toString: String = inspect match {
    case Left(cls) => s"${cls}:${System.identityHashCode(this)}"
    case Right(ty) => ty.toString
  }
}

object TypeSymbol {
  val INTEGRAL = new TypeSymbol(DataType.INTEGRAL)
  val FLOAT = new TypeSymbol(DataType.FLOAT)
  val STRING = new TypeSymbol(DataType.STRING)

  def const(constType: DataType): TypeSymbol = constType match {
    case DataType.INTEGRAL => INTEGRAL
    case DataType.FLOAT => FLOAT
    case DataType.STRING => STRING
  }
}

case class TypeConstraints[V](table: Map[V, TypeSymbol]) {
  def ++(that: TypeConstraints[V]): TypeConstraints[V] =
    TypeConstraints((this.table.keySet ++ that.table.keySet).map(v => {
      v -> ((this.table.get(v), that.table.get(v)) match {
        case (Some(ty1), None) => ty1
        case (None, Some(ty2)) => ty2
        case (Some(ty1), Some(ty2)) => ty1.unify(ty2)
        case _ => throw new Exception("unreachable")
      })
    }).toMap)
}

sealed trait Term[V] extends Serializable {
  def freeVariables: Set[V]
  def freeVariablesInOrder: Seq[V]
  def inferType(signature: Signature): (TypeConstraints[V], TypeSymbol)
  def map[W](mapper: VariableMapper[V, W]): Term[W]
  def toQTL:String
}

case class Const[V](value: Any) extends Term[V] {
  override val freeVariables: Set[V] = Set.empty
  override val freeVariablesInOrder: Seq[V] = Seq.empty

  val valueType: DataType = value match {
    // TODO(JS): In the Fact class we don't support Integer arguments.
    case _: java.lang.Integer => DataType.INTEGRAL
    case _: java.lang.Long => DataType.INTEGRAL
    case _: java.lang.Double => DataType.FLOAT
    case _: java.lang.String => DataType.STRING
  }

  override def inferType(signature: Signature): (TypeConstraints[V], TypeSymbol) =
    (TypeConstraints(Map.empty), TypeSymbol.const(valueType))

  override def map[W](mapper: VariableMapper[V, W]): Const[W] = Const(value)
  override def toString: String = value.toString
  override def toQTL: String = value match {
    case s: String => "\"" + s + "\""
    case _ => value.toString
  }
}

case class Var[V](variable: V) extends Term[V] {
  override val freeVariables: Set[V] = Set(variable)
  override val freeVariablesInOrder: Seq[V] = Seq(variable)

  override def inferType(signature: Signature): (TypeConstraints[V], TypeSymbol) = {
    val symbol = new TypeSymbol(AnyClass())
    (TypeConstraints(Map(variable -> symbol)), symbol)
  }

  override def map[W](mapper: VariableMapper[V, W]): Var[W] = Var(mapper.map(variable))
  override def toString: String = variable.toString
  override def toQTL: String = toString
}

sealed trait Apply[V] extends Term[V] {
  val f: MFOTLFunction
}

case class Apply1[V](f: MFOTLFunction, t: Term[V]) extends Apply[V] {
  override val freeVariables: Set[V] = t.freeVariables
  override val freeVariablesInOrder: Seq[V] = t.freeVariablesInOrder

  override def inferType(signature: Signature): (TypeConstraints[V], TypeSymbol) = {
    val (tc, tty) = t.inferType(signature)
    f match {
      case F2I() => tty.unify(TypeSymbol.FLOAT); (tc, TypeSymbol.INTEGRAL)
      case I2F() => tty.unify(TypeSymbol.INTEGRAL); (tc, TypeSymbol.FLOAT)
      case MINUS() => (tc, tty.enforceNumeric())
      case _ => throw new Exception("Unexpected unary operator " + f.op)
    }
  }

  override def map[W](mapper: VariableMapper[V, W]): Apply1[W] = Apply1(f,t.map(mapper))
  override def toString: String = s"$f($t)"
  override def toQTL: String = throw new UnsupportedOperationException("Functional terms in QTL")
}

case class Apply2[V](f: MFOTLFunction, t1: Term[V],t2: Term[V]) extends Apply[V] {
  override val freeVariables: Set[V] = t1.freeVariables union t2.freeVariables
  override val freeVariablesInOrder: Seq[V] = t1.freeVariablesInOrder ++ t2.freeVariablesInOrder

  override def inferType(signature: Signature): (TypeConstraints[V], TypeSymbol) = {
    val (tc1, tty1) = t1.inferType(signature)
    val (tc2, tty2) = t2.inferType(signature)
    val tc = tc1 ++ tc2
    (tc, tty1.enforceNumeric().unify(tty2))
  }

  override def map[W](mapper: VariableMapper[V, W]): Apply2[W] = Apply2(f,t1.map(mapper),t2.map(mapper))
  override def toString: String = s"$t1$f$t2"
  override def toQTL: String = throw new UnsupportedOperationException("Functional terms in QTL")
}

sealed trait MFOTLFunction{
  val op:String
  override def toString:String = s" $op "
}
case class F2I() extends MFOTLFunction{
  val op = "f2i"
}
case class I2F() extends MFOTLFunction{
  val op = "i2f"
}
case class PLUS() extends MFOTLFunction{
  val op = "+"
}
case class MINUS() extends MFOTLFunction{
  val op = "-"
}
case class TIMES() extends MFOTLFunction{
  val op = "*"
}
case class DIV() extends MFOTLFunction{
  val op = "/"
}
case class MOD() extends MFOTLFunction{
  val op = "MOD"
}


/***
  * Intervals for temporal operators.
  * Lower bound is inclusive, upper bound is exclusive.
  */
case class Interval(lower: Int, upper: Option[Int]) {
  
  def check: List[String] =
    // TODO(JS): Do we want to allow empty intervals?
    if (upper.isDefined && upper.get <= lower) List(s"$this is not a valid interval")
    else if (lower < 0) List(s"interval $this contains negative values")
    else Nil

  override def toString: String = upper match {
    case None => s"[$lower,*)"
    case Some(u) => s"[$lower,$u)"
  }
  def toQTL:String = 
    // [lower, upper) = (lower-1, upper) = (lower-1, upper-1]
    (lower, upper) match {
      case (0,None) => ""
      case (l,None) => s"[> ${l-1} ]"
      case (0,Some(u)) => s"[<= ${u-1} ]"
      case erri @ _ => throw new UnsupportedOperationException(s"Double-bounded intervals are not supported in QTL: ${erri}")
    }
}

object Interval {
  val any = Interval(0, None)
}

sealed trait GenFormula[V] extends Serializable {

  def atoms: Set[Pred[V]]
  def atomsInOrder: Seq[Pred[V]]
  def freeVariables: Set[V]
  def freeVariablesInOrder: Seq[V]
  def inferTypes(signature: Signature): TypeConstraints[V]
  def map[W](mapper: VariableMapper[V, W]): GenFormula[W]
  def intervalCheck: List[String]

  def freeVariableTypes(signature: Signature): Map[V, DataType] = {
    val typing = inferTypes(signature).table
    freeVariables.map(v => typing(v).inspect match {
      case Left(_) => throw new Exception("Variable " + v + " is polymorphic")
      case Right(t) => v -> t
    }).toMap
  }

  def translateToQTL(epred: Pred[String]): (GenFormula[String], Map[Pred[String],GenFormula[String]]) = {
    val phi0 = this.asInstanceOf[GenFormula[String]]

    // MFOTL LET is a non-recursive definition, so it can be eliminated by substitution.
    // DejaVu macros cannot express it directly: their expansion requires the call-site
    // argument names to coincide with the head parameter names.
    val phi1 = GenFormula.expandLets(phi0)

    if (phi1.atoms.exists(_.relation == epred.relation))
      throw new UnsupportedOperationException(
        s"The formula must not use the event predicate '${epred.relation}', which marks database boundaries in the translated trace")

    for ((rel, preds) <- phi1.atoms.groupBy(_.relation) if preds.map(_.args.length).size > 1)
      throw new UnsupportedOperationException(
        s"Predicate '${rel}' is used with different arities; DejaVu matches events by name only")

    // DejaVu rejects two quantifiers with the same variable name in one formula.
    val phi = GenFormula.uniquifyBoundVariables(phi1)

    def distinctVarArgs(args: Seq[Term[String]]): Boolean = {
      val vars = args.collect { case Var(v) => v }
      vars.length == args.length && vars.distinct.length == vars.length
    }

    // Lifts a predicate occurrence to the database boundary: e() AND PREVIOUS ((NOT e()) SINCE p).
    def lifted(p: Pred[String]): GenFormula[String] =
      And(epred, Prev(Interval.any, Since(Interval.any, Not(epred), p)))

    // One let per predicate and argument combination, because DejaVu macro expansion is
    // name-sensitive. Occurrences with constant or repeated arguments get no let: DejaVu
    // rejects such macro heads, so rho inlines the lifted formula at those occurrences.
    def predsToLets(f: GenFormula[String],
                    lets: ListMap[Pred[String],GenFormula[String]]): ListMap[Pred[String],GenFormula[String]] = f match {
      case True() | False() | Rel(_, _, _) => lets
      case p @ Pred(pn, args @ _*) =>
        if (distinctVarArgs(args) && !lets.contains(Pred("_" + pn, args:_*)))
          lets + (Pred("_" + pn, args:_*) -> lifted(p))
        else lets
      case Not(arg) => predsToLets(arg, lets)
      case And(arg1, arg2) => predsToLets(arg2, predsToLets(arg1, lets))
      case Or(arg1, arg2) => predsToLets(arg2, predsToLets(arg1, lets))
      case All(_, arg) => predsToLets(arg, lets)
      case Ex(_, arg) => predsToLets(arg, lets)
      case Prev(_, arg) => predsToLets(arg, lets)
      case Next(_, arg) => predsToLets(arg, lets)
      case Since(_, arg1, arg2) => predsToLets(arg2, predsToLets(arg1, lets))
      case Trigger(_, arg1, arg2) => predsToLets(arg2, predsToLets(arg1, lets))
      case Until(_, arg1, arg2) => predsToLets(arg2, predsToLets(arg1, lets))
      case Release(_, arg1, arg2) => predsToLets(arg2, predsToLets(arg1, lets))
      case errf @ _ => throw new UnsupportedOperationException(s"Operator not supported in the QTL translation: ${errf}")
    }

    val letsMap = predsToLets(phi, ListMap.empty)

    // Every formula produced by rho holds only at positions where e() holds. This invariant is
    // what makes the SINCE and PREVIOUS cases below correct, so the leaves that are true at
    // arbitrary positions (TRUE, equality, negation) must be guarded with e().
    def rho(f: GenFormula[String]): GenFormula[String] = f match {
      case True() => epred
      case False() => False()
      // DejaVu only accepts =, <, <=, >, >= with the variable on the left-hand side.
      case Rel(op @ (EQ() | LT() | LE() | GT() | GE()), t1, t2) => (t1, t2) match {
        case (c @ Const(_), x @ Var(_)) => And(Rel(GenFormula.mirror(op), x, c), epred)
        case (Const(a), Const(b)) => if (GenFormula.evalRel(op, a, b)) epred else False()
        case _ => And(Rel(op, t1, t2), epred)
      }
      case p @ Pred(relation, args @ _*) =>
        if (distinctVarArgs(args)) Pred("_" + relation, args:_*) else lifted(p)
      case Not(arg) => And(Not(rho(arg)), epred)
      case And(arg1, arg2) => And(rho(arg1), rho(arg2))
      case Or(arg1, arg2) => Or(rho(arg1), rho(arg2))
      case All(bound, arg) => All(bound, rho(arg))
      case Ex(bound, arg) => Ex(bound, rho(arg))
      // The metric constraint sits on the inner SINCE, which measures the time from the
      // previous e() to the last event of the current database. This equals the MFOTL
      // timestamp difference unless the current database is empty.
      case Prev(i, arg) => And(epred, Prev(Interval.any, Since(i, Not(epred), rho(arg))))
      case Since(i, arg1, arg2) => And(Since(i, Or(rho(arg1), Not(epred)), rho(arg2)), epred)
      case errf @ _ => throw new UnsupportedOperationException(s"Operator not supported in the QTL translation: ${errf}")
    }

    (rho(phi), letsMap)
  }

  def toQTLString(neg:Boolean, epred: Pred[String]):String = {
    val (fma,lets) = this.translateToQTL(epred)
    val closed = fma.freeVariables.toList.sorted.foldLeft(fma) {
      (acc, v) => if (neg) Ex(v, acc) else All(v, acc)
    }
    // Without the negation, the formula is relativized to e() positions: DejaVu evaluates the
    // property at every event, and the raw events between two e()s must not count as verdicts.
    val f = if (neg) Not(closed) else GenFormula.implies(epred, closed)
    val letsStr =
      if (lets.isEmpty) ""
      else " where " + lets.map{ case (p, body) => s"${p.toQTL} := ${body.toQTL}"}.mkString(", ")
    "prop fma: " + f.toQTL + letsStr
  }
  def toQTL:String
}

sealed trait Operator{
 val op:String
 override def toString:String = s" $op "
}
case class EQ() extends Operator{
 val op = "="
}
case class LT() extends Operator{
 val op = "<"
}
case class LE() extends Operator{
 val op = "<="
}
case class GT() extends Operator{
 val op = ">"
}
case class GE() extends Operator{
 val op = ">="
}
case class SUBSTRING() extends Operator{
 val op = "SUBSTRING"
}
case class MATCHES() extends Operator{
 val op = "MATCHES"
}

case class Rel[V](op:Operator, arg1: Term[V],arg2: Term[V]) extends GenFormula[V]{
 override def atoms: Set[Pred[V]] = Set()
 override def atomsInOrder: Seq[Pred[V]] = Seq()
 override def freeVariables: Set[V] = arg1.freeVariables ++ arg2.freeVariables
 override def freeVariablesInOrder: Seq[V] = arg1.freeVariablesInOrder ++ arg2.freeVariablesInOrder
 override def inferTypes(signature: Signature): TypeConstraints[V] = {
   val (tc1, tty1) = arg1.inferType(signature)
   val (tc2, tty2) = arg2.inferType(signature)
   val tc = tc1 ++ tc2
   op match{
    case EQ() => tty1.unify(tty2)
    case SUBSTRING() | MATCHES() => 
      tty1.unify(TypeSymbol.const(DataType.STRING))
      tty2.unify(TypeSymbol.const(DataType.STRING))
    case LT() | LE() | GT() | GE() => 
      tty1.enforceNumeric().unify(tty2.enforceNumeric())
   }
   tc
 }
 override def map[W](mapper: VariableMapper[V, W]): GenFormula[W] = Rel(op,arg1.map(mapper),arg2.map(mapper))
 override def intervalCheck: List[String] = Nil
 override def toString: String = s"${arg1} ${op} ${arg2}"
 override def toQTL: String = op match{
  case EQ() | LT() | LE() | GT() | GE() => s"${arg1.toQTL} ${op.op} ${arg2.toQTL}"
  case _ => throw new UnsupportedOperationException(s"Relational operator${op}is not supported in QTL")
 }
}

case class True[V]() extends GenFormula[V] {
  override val atoms: Set[Pred[V]] = Set.empty
  override val atomsInOrder: Seq[Pred[V]] = Seq.empty
  override val freeVariables: Set[V] = Set.empty
  override val freeVariablesInOrder: Seq[V] = Seq.empty
  override def inferTypes(signature: Signature): TypeConstraints[V] = TypeConstraints(Map.empty)
  override def map[W](mapper: VariableMapper[V, W]): True[W] = True()
  override def intervalCheck: List[String] = Nil
  override def toString: String = "TRUE"
  override def toQTL: String = "true"
}

case class False[V]() extends GenFormula[V] {
  override val atoms: Set[Pred[V]] = Set.empty
  override val atomsInOrder: Seq[Pred[V]] = Seq.empty
  override val freeVariables: Set[V] = Set.empty
  override val freeVariablesInOrder: Seq[V] = Seq.empty
  override def inferTypes(signature: Signature): TypeConstraints[V] = TypeConstraints(Map.empty)
  override def map[W](mapper: VariableMapper[V, W]): False[W] = False()
  override def intervalCheck: List[String] = Nil
  override def toString: String = "FALSE"
  override def toQTL: String = "false"
}

case class Pred[V](relation: String, args: Term[V]*) extends GenFormula[V] {
  override val atoms: Set[Pred[V]] = Set(this)
  override val atomsInOrder: Seq[Pred[V]] = Seq(this)
  override lazy val freeVariables: Set[V] = args.flatMap(_.freeVariables).toSet
  override lazy val freeVariablesInOrder: Seq[V] = args.flatMap(_.freeVariables)

  override def inferTypes(signature: Signature): TypeConstraints[V] = {
    val (tcs, ttys) = args.map(_.inferType(signature)).unzip
    val tc = tcs.fold(TypeConstraints[V](Map.empty))(_ ++ _)

    for ((ty, cty) <- ttys zip signature((relation, args.length))) {
      ty.unify(TypeSymbol.const(cty))
    }
    tc
  }

  override def map[W](mapper: VariableMapper[V, W]): Pred[W] = Pred(relation, args.map(_.map(mapper)):_*)
  override def intervalCheck: List[String] = Nil
  override def toString: String = s"$relation(${args.mkString(", ")})"
  override def toQTL: String = s"$relation(${args.map(_.toQTL).mkString(", ")})"
}

case class Not[V](arg: GenFormula[V]) extends GenFormula[V] {
  override lazy val atoms: Set[Pred[V]] = arg.atoms
  override lazy val atomsInOrder: Seq[Pred[V]] = arg.atomsInOrder
  override lazy val freeVariables: Set[V] = arg.freeVariables
  override lazy val freeVariablesInOrder: Seq[V] = arg.freeVariablesInOrder

  override def inferTypes(signature: Signature): TypeConstraints[V] =
    arg.inferTypes(signature)

  override def map[W](mapper: VariableMapper[V, W]): Not[W] = Not(arg.map(mapper))
  override def intervalCheck: List[String] = arg.intervalCheck
  override def toString: String = s"NOT ($arg)"
  override def toQTL: String = s"! ${GenFormula.toParenthesizedQTL(arg)}"
}

case class And[V](arg1: GenFormula[V], arg2: GenFormula[V]) extends GenFormula[V] {
  override lazy val atoms: Set[Pred[V]] = arg1.atoms ++ arg2.atoms
  override lazy val atomsInOrder: Seq[Pred[V]] = arg1.atomsInOrder ++ arg2.atomsInOrder
  override lazy val freeVariables: Set[V] = arg1.freeVariables ++ arg2.freeVariables
  override lazy val freeVariablesInOrder: Seq[V] = arg1.freeVariablesInOrder ++ arg2.freeVariablesInOrder

  override def inferTypes(signature: Signature): TypeConstraints[V] =
    arg1.inferTypes(signature) ++ arg2.inferTypes(signature)

  override def map[W](mapper: VariableMapper[V, W]): And[W] = And(arg1.map(mapper), arg2.map(mapper))
  override def intervalCheck: List[String] = arg1.intervalCheck ++ arg2.intervalCheck
  override def toString: String = s"($arg1) AND ($arg2)"
  override def toQTL: String = s"${GenFormula.toParenthesizedQTL(arg1)} & ${GenFormula.toParenthesizedQTL(arg2)}"
}

case class Or[V](arg1: GenFormula[V], arg2: GenFormula[V]) extends GenFormula[V] {
  override lazy val atoms: Set[Pred[V]] = arg1.atoms ++ arg2.atoms
  override lazy val atomsInOrder: Seq[Pred[V]] = arg1.atomsInOrder ++ arg2.atomsInOrder
  override lazy val freeVariables: Set[V] = arg1.freeVariables ++ arg2.freeVariables
  override lazy val freeVariablesInOrder: Seq[V] = arg1.freeVariablesInOrder ++ arg2.freeVariablesInOrder

  override def inferTypes(signature: Signature): TypeConstraints[V] =
    arg1.inferTypes(signature) ++ arg2.inferTypes(signature)

  override def map[W](mapper: VariableMapper[V, W]): Or[W] = Or(arg1.map(mapper), arg2.map(mapper))
  override def intervalCheck: List[String] = arg1.intervalCheck ++ arg2.intervalCheck
  override def toString: String = s"($arg1) OR ($arg2)"
  override def toQTL: String = s"${GenFormula.toParenthesizedQTL(arg1)} | ${GenFormula.toParenthesizedQTL(arg2)}"
}

case class All[V](variable: V, arg: GenFormula[V]) extends GenFormula[V] {
  override lazy val atoms: Set[Pred[V]] = arg.atoms
  override lazy val atomsInOrder: Seq[Pred[V]] = arg.atomsInOrder
  override lazy val freeVariables: Set[V] = arg.freeVariables - variable
  override lazy val freeVariablesInOrder: Seq[V] = arg.freeVariablesInOrder.filter(_ != variable)

  override def inferTypes(signature: Signature): TypeConstraints[V] =
    arg.inferTypes(signature)

  override def map[W](mapper: VariableMapper[V, W]): All[W] = {
    val (newVariable, innerMapper) = mapper.bound(variable)
    All(newVariable, arg.map(innerMapper))
  }

  override def intervalCheck: List[String] = arg.intervalCheck
  override def toString: String = s"FORALL $variable. $arg"
  override def toQTL: String = s"Forall ${Var(variable).toQTL}. ${GenFormula.toParenthesizedQTL(arg)}"

}

case class Ex[V](variable: V, arg: GenFormula[V]) extends GenFormula[V] {
  override lazy val atoms: Set[Pred[V]] = arg.atoms
  override lazy val atomsInOrder: Seq[Pred[V]] = arg.atomsInOrder
  override lazy val freeVariables: Set[V] = arg.freeVariables - variable
  override lazy val freeVariablesInOrder: Seq[V] = arg.freeVariablesInOrder.filter(_ != variable)

  override def inferTypes(signature: Signature): TypeConstraints[V] =
    arg.inferTypes(signature)

  override def map[W](mapper: VariableMapper[V, W]): Ex[W] = {
    val (newVariable, innerMapper) = mapper.bound(variable)
    Ex(newVariable, arg.map(innerMapper))
  }

  override def intervalCheck: List[String] = arg.intervalCheck
  override def toString: String = s"EXISTS $variable. $arg"
  override def toQTL: String = s"Exists ${Var(variable).toQTL}. ${GenFormula.toParenthesizedQTL(arg)}"

}

case class Prev[V](interval: Interval, arg: GenFormula[V]) extends GenFormula[V] {
  override lazy val atoms: Set[Pred[V]] = arg.atoms
  override lazy val atomsInOrder: Seq[Pred[V]] = arg.atomsInOrder
  override lazy val freeVariables: Set[V] = arg.freeVariables
  override lazy val freeVariablesInOrder: Seq[V] = arg.freeVariablesInOrder

  override def inferTypes(signature: Signature): TypeConstraints[V] =
    arg.inferTypes(signature)

  override def map[W](mapper: VariableMapper[V, W]): Prev[W] = Prev(interval, arg.map(mapper))
  override def intervalCheck: List[String] = interval.check ++ arg.intervalCheck
  override def toString: String = s"PREVIOUS $interval ($arg)"
  override def toQTL: String = s"@ ${interval.toQTL} ${GenFormula.toParenthesizedQTL(arg)}"
}

case class Next[V](interval: Interval, arg: GenFormula[V]) extends GenFormula[V] {
  override lazy val atoms: Set[Pred[V]] = arg.atoms
  override lazy val atomsInOrder: Seq[Pred[V]] = arg.atomsInOrder
  override lazy val freeVariables: Set[V] = arg.freeVariables
  override lazy val freeVariablesInOrder: Seq[V] = arg.freeVariablesInOrder

  override def inferTypes(signature: Signature): TypeConstraints[V] =
    arg.inferTypes(signature)

  override def map[W](mapper: VariableMapper[V, W]): Next[W] = Next(interval, arg.map(mapper))
  override def intervalCheck: List[String] = interval.check ++ arg.intervalCheck
  override def toString: String = s"NEXT $interval ($arg)"
  override def toQTL: String = throw new UnsupportedOperationException("Next operator not supported in QTL")
}

case class Since[V](interval: Interval, arg1: GenFormula[V], arg2: GenFormula[V]) extends GenFormula[V] {
  override lazy val atoms: Set[Pred[V]] = arg1.atoms ++ arg2.atoms
  override lazy val atomsInOrder: Seq[Pred[V]] = arg1.atomsInOrder ++ arg2.atomsInOrder
  override lazy val freeVariables: Set[V] = arg1.freeVariables ++ arg2.freeVariables
  override lazy val freeVariablesInOrder: Seq[V] = arg2.freeVariablesInOrder ++ arg1.freeVariablesInOrder

  override def inferTypes(signature: Signature): TypeConstraints[V] =
    arg1.inferTypes(signature) ++ arg2.inferTypes(signature)

  override def map[W](mapper: VariableMapper[V, W]): Since[W] = Since(interval, arg1.map(mapper), arg2.map(mapper))
  override def intervalCheck: List[String] = arg1.intervalCheck ++ interval.check ++ arg2.intervalCheck
  override def toString: String = s"($arg1) SINCE $interval ($arg2)"
  override def toQTL: String = if (!arg1.equals(True[V]())) 
      s"${GenFormula.toParenthesizedQTL(arg1)} S ${interval.toQTL} ${GenFormula.toParenthesizedQTL(arg2)}" 
    else 
      s"P ${interval.toQTL} ${GenFormula.toParenthesizedQTL(arg2)}"
}

case class Trigger[V](interval: Interval, arg1: GenFormula[V], arg2: GenFormula[V]) extends GenFormula[V] {
  override lazy val atoms: Set[Pred[V]] = arg1.atoms ++ arg2.atoms
  override lazy val atomsInOrder: Seq[Pred[V]] = arg1.atomsInOrder ++ arg2.atomsInOrder
  override lazy val freeVariables: Set[V] = arg1.freeVariables ++ arg2.freeVariables
  override lazy val freeVariablesInOrder: Seq[V] = arg2.freeVariablesInOrder ++ arg1.freeVariablesInOrder

  override def inferTypes(signature: Signature): TypeConstraints[V] =
    arg1.inferTypes(signature) ++ arg2.inferTypes(signature)

  override def map[W](mapper: VariableMapper[V, W]): Trigger[W] = Trigger(interval, arg1.map(mapper), arg2.map(mapper))
  override def intervalCheck: List[String] = arg1.intervalCheck ++ interval.check ++ arg2.intervalCheck
  override def toString: String = s"($arg1) TRIGGER $interval ($arg2)"
  override def toQTL: String = Not(Since(interval, Not(arg1), Not(arg2))).toQTL
}

case class Until[V](interval: Interval, arg1: GenFormula[V], arg2: GenFormula[V]) extends GenFormula[V] {
  override lazy val atoms: Set[Pred[V]] = arg1.atoms ++ arg2.atoms
  override lazy val atomsInOrder: Seq[Pred[V]] = arg1.atomsInOrder ++ arg2.atomsInOrder
  override lazy val freeVariables: Set[V] = arg1.freeVariables ++ arg2.freeVariables
  override lazy val freeVariablesInOrder: Seq[V] = arg2.freeVariablesInOrder ++ arg1.freeVariablesInOrder

  override def inferTypes(signature: Signature): TypeConstraints[V] =
    arg1.inferTypes(signature) ++ arg2.inferTypes(signature)

  override def map[W](mapper: VariableMapper[V, W]): Until[W] = Until(interval, arg1.map(mapper), arg2.map(mapper))
  override def intervalCheck: List[String] = arg1.intervalCheck ++ interval.check ++ arg2.intervalCheck
  override def toString: String = s"($arg1) UNTIL $interval ($arg2)"
  override def toQTL: String = throw new UnsupportedOperationException("Until operator not supported in QTL")
}

case class Release[V](interval: Interval, arg1: GenFormula[V], arg2: GenFormula[V]) extends GenFormula[V] {
  override lazy val atoms: Set[Pred[V]] = arg1.atoms ++ arg2.atoms
  override lazy val atomsInOrder: Seq[Pred[V]] = arg1.atomsInOrder ++ arg2.atomsInOrder
  override lazy val freeVariables: Set[V] = arg1.freeVariables ++ arg2.freeVariables
  override lazy val freeVariablesInOrder: Seq[V] = arg2.freeVariablesInOrder ++ arg1.freeVariablesInOrder

  override def inferTypes(signature: Signature): TypeConstraints[V] =
    arg1.inferTypes(signature) ++ arg2.inferTypes(signature)

  override def map[W](mapper: VariableMapper[V, W]): Release[W] = Release(interval, arg1.map(mapper), arg2.map(mapper))
  override def intervalCheck: List[String] = arg1.intervalCheck ++ interval.check ++ arg2.intervalCheck
  override def toString: String = s"($arg1) RELEASE $interval ($arg2)"
  override def toQTL: String = throw new UnsupportedOperationException("Release operator not supported in QTL")
}

case class Let[V](p:Pred[V],f:GenFormula[V], g:GenFormula[V]) extends GenFormula[V]{
  require(p.freeVariables == f.freeVariables)

  override def atoms: Set[Pred[V]] = {
    val (inst, rest) = g.atoms.partition{ _.relation == p.relation}
    val repl = f.atoms.flatMap(GenFormula.explode(_,inst))
    repl union rest
  }
  override def atomsInOrder: Seq[Pred[V]] = {
    val (inst, rest) = g.atomsInOrder.partition{ _.relation == p.relation}
    val repl = f.atomsInOrder.flatMap(GenFormula.explode(_,inst.toIterable))
    repl ++ rest
  }
  override def freeVariables: Set[V] = g.freeVariables
  override def freeVariablesInOrder: Seq[V] = g.freeVariablesInOrder

  override def inferTypes(signature: Signature): TypeConstraints[V] = {
    val fTypes = f.freeVariableTypes(signature)
    val pTypes = p.args.map({case Var(v) => fTypes(v); case _ => throw new Exception("Unexpected term")})
    g.inferTypes(signature + ((p.relation, p.args.length) -> pTypes))
  }

  override def map[W](mapper: VariableMapper[V, W]): GenFormula[W] = {
    val m = p.freeVariablesInOrder.foldLeft(mapper){
      (a:VariableMapper[V, W],v:V) => a.bound(v)._2
    }
    Let(p.map(m),f.map(m),g.map(mapper))
  }
  override def intervalCheck: List[String] = p.intervalCheck ++ f.intervalCheck ++ g.intervalCheck
  override def toString: String = s"LET ${p} = ${f} IN \n ${g}"
  override def toQTL: String = g.toQTL ++ " where " ++ p.toQTL ++ " := " ++ f.toQTL
}

sealed trait AggregateFunction{
  val op:String
  override def toString:String = s" $op "
  val argConstraint: TypeClass
  val resultType: Option[DataType]
}
case class CNT() extends AggregateFunction{
  val op = "CNT"

  override val argConstraint: TypeClass = AnyClass()
  override val resultType: Option[DataType] = Some(DataType.INTEGRAL)
}
case class SUM() extends AggregateFunction{
  val op = "SUM"

  override val argConstraint: TypeClass = NumericClass()
  override val resultType: Option[DataType] = None
}
case class AVG() extends AggregateFunction{
  val op = "AVG"

  override val argConstraint: TypeClass = NumericClass()
  override val resultType: Option[DataType] = Some(DataType.FLOAT)
}
case class MIN() extends AggregateFunction{
  val op = "MIN"

  override val argConstraint: TypeClass = AnyClass()
  override val resultType: Option[DataType] = None
}
case class MAX() extends AggregateFunction{
  val op = "MAX"

  override val argConstraint: TypeClass = AnyClass()
  override val resultType: Option[DataType] = None
}
case class MED() extends AggregateFunction{
  val op = "MED"

  override val argConstraint: TypeClass = NumericClass()
  override val resultType: Option[DataType] = Some(DataType.FLOAT)
}


case class Aggr[V](r:Var[V], af:AggregateFunction, x:Var[V], f:GenFormula[V], gs: Seq[Var[V]]) extends GenFormula[V] {
  require(gs.map(_.variable).toSet subsetOf f.freeVariables)
  require((f.freeVariables contains x.variable) || af.isInstanceOf[CNT])
  override def atoms: Set[Pred[V]] = f.atoms
  override def atomsInOrder: Seq[Pred[V]] = f.atomsInOrder
  override def freeVariables: Set[V] = Set(r.variable) ++ gs.map(_.variable).toSet
  override def freeVariablesInOrder: Seq[V] = Seq(r.variable) ++ gs.map(_.variable)

  override def inferTypes(signature: Signature): TypeConstraints[V] = {
    val xty = new TypeSymbol(af.argConstraint)
    val rty = af.resultType match {
      case None => xty
      case Some(ty) => TypeSymbol.const(ty)
    }
    f.inferTypes(signature) ++ TypeConstraints(Map(r.variable -> rty, x.variable -> xty))
  }

  override def map[W](mapper: VariableMapper[V, W]): GenFormula[W] = {
    val bvs = f.freeVariables diff (gs.map(_.variable).toSet)
    val innerMapper = bvs.foldLeft(mapper)((m,v) => m.bound(v)._2)
    val aggMapper = if (gs contains x) mapper else innerMapper
    Aggr(r.map(mapper),af,x.map(aggMapper),f.map(innerMapper),gs.map(_.map(mapper)))
  }
  override def intervalCheck: List[String] = f.intervalCheck
  override def toString: String =
    if(gs.isEmpty) s"$r <- $af $x $f"
    else  s"$r <- $af $x; ${gs.mkString(",")} $f"
  override def toQTL: String = throw new UnsupportedOperationException("Aggregations not supported in QTL")
}

object GenFormula {
  type Signature = Map[(String, Int), Seq[DataType]]

  def implies[V](arg1: GenFormula[V], arg2: GenFormula[V]): GenFormula[V] = Or(Not(arg1), arg2)
  def equiv[V](arg1: GenFormula[V], arg2: GenFormula[V]): GenFormula[V] = And(implies(arg1, arg2), implies(arg2, arg1))
  def once[V](interval: Interval = Interval.any, arg: GenFormula[V]): GenFormula[V] = Since(interval, True(), arg)
  def historically[V](interval: Interval = Interval.any, arg: GenFormula[V]): GenFormula[V] = Trigger(interval, False(), arg)
  def eventually[V](interval: Interval = Interval.any, arg: GenFormula[V]): GenFormula[V] = Until(interval, True(), arg)
  def always[V](interval: Interval = Interval.any, arg: GenFormula[V]): GenFormula[V] = Release(interval, False(), arg)
  def ex[V](vs:Seq[Var[V]], arg:GenFormula[V]):GenFormula[V] = vs.foldRight(arg)((v,a) => Ex[V](v.variable,a))
  def all[V](vs:Seq[Var[V]], arg:GenFormula[V]):GenFormula[V] = vs.foldRight(arg)((v,a) => All[V](v.variable,a))
  def eql[V](t1:Term[V],t2:Term[V]):GenFormula[V] = Rel(EQ(),t1,t2)
  def lte[V](t1:Term[V],t2:Term[V]):GenFormula[V] = Rel(LT(),t1,t2)
  def leq[V](t1:Term[V],t2:Term[V]):GenFormula[V] = Rel(LE(),t1,t2)
  def gte[V](t1:Term[V],t2:Term[V]):GenFormula[V] = Rel(GT(),t1,t2)
  def geq[V](t1:Term[V],t2:Term[V]):GenFormula[V] = Rel(GE(),t1,t2)
  def substr[V](t1:Term[V],t2:Term[V]):GenFormula[V] = Rel(SUBSTRING(),t1,t2)
  def matches[V](t1:Term[V],t2:Term[V]):GenFormula[V] = Rel(MATCHES(),t1,t2)

  def i2f[V](t:Term[V]):Term[V] = Apply1(I2F(),t)
  def f2i[V](t:Term[V]):Term[V] = Apply1(F2I(),t)
  def plus[V](t1:Term[V],t2:Term[V]):Term[V] = Apply2(PLUS(),t1,t2)
  def minus[V](t1:Term[V],t2:Term[V]):Term[V] = Apply2(MINUS(),t1,t2)
  def times[V](t1:Term[V],t2:Term[V]):Term[V] = Apply2(TIMES(),t1,t2)
  def div[V](t1:Term[V],t2:Term[V]):Term[V] = Apply2(DIV(),t1,t2)
  def mod[V](t1:Term[V],t2:Term[V]):Term[V] = Apply2(MOD(),t1,t2)

  def resolve(phi: GenFormula[String]): GenFormula[VariableID[String]] = {
    val freeVariables: Map[String, VariableID[String]] =
      phi.freeVariables.toSeq.sorted.zipWithIndex.map{ case (n, i) => (n, new VariableID(n, i)) }(collection.breakOut)
    phi.map(new VariableResolver(freeVariables))
  }

  /** The operator for the mirrored relation: c op x is equivalent to x (mirror op) c. */
  def mirror(op: Operator): Operator = op match {
    case LT() => GT()
    case LE() => GE()
    case GT() => LT()
    case GE() => LE()
    case other => other
  }

  private def numericValue(v: Any): Option[BigDecimal] = v match {
    case i: java.lang.Integer => Some(BigDecimal(i.intValue()))
    case l: java.lang.Long => Some(BigDecimal(l.longValue()))
    case d: java.lang.Double => Some(BigDecimal(d.doubleValue()))
    case _ => None
  }

  /** Statically evaluates a relation between two constants. */
  def evalRel(op: Operator, a: Any, b: Any): Boolean = op match {
    case EQ() => a == b
    case LT() | LE() | GT() | GE() => (numericValue(a), numericValue(b)) match {
      case (Some(x), Some(y)) => op match {
        case LT() => x < y
        case LE() => x <= y
        case GT() => x > y
        case GE() => x >= y
        case _ => throw new IllegalStateException("unreachable")
      }
      case _ => throw new UnsupportedOperationException(
        s"Ordering comparison of non-numeric constants: ${a}${op}${b}")
    }
    case _ => throw new UnsupportedOperationException(s"Relational operator${op}is not supported in QTL")
  }

  private def substituteTerm(t: Term[String], m: Map[String, Term[String]]): Term[String] = t match {
    case Var(v) => m.getOrElse(v, Var(v))
    case c @ Const(_) => c
    case Apply1(f, t1) => Apply1(f, substituteTerm(t1, m))
    case Apply2(f, t1, t2) => Apply2(f, substituteTerm(t1, m), substituteTerm(t2, m))
  }

  private def freshAvoiding(hint: String, avoid: Set[String]): String =
    if (!avoid(hint)) hint
    else Stream.from(1).map(i => s"${hint}_$i").find(!avoid(_)).get

  /** Capture-avoiding substitution of free variables by terms. */
  def substituteVars(phi: GenFormula[String], m: Map[String, Term[String]]): GenFormula[String] = {
    val rangeVars: Set[String] = m.values.flatMap(_.freeVariables).toSet
    def quant(v: String, arg: GenFormula[String], m: Map[String, Term[String]],
              mk: (String, GenFormula[String]) => GenFormula[String]): GenFormula[String] = {
      val m1 = m - v
      if (rangeVars(v)) {
        val nv = freshAvoiding(v, rangeVars ++ arg.freeVariables ++ m1.keySet)
        mk(nv, go(arg, m1 + (v -> Var(nv))))
      } else mk(v, go(arg, m1))
    }
    def go(f: GenFormula[String], m: Map[String, Term[String]]): GenFormula[String] = f match {
      case True() | False() => f
      case Rel(op, t1, t2) => Rel(op, substituteTerm(t1, m), substituteTerm(t2, m))
      case Pred(r, args @ _*) => Pred(r, args.map(substituteTerm(_, m)):_*)
      case Not(arg) => Not(go(arg, m))
      case And(arg1, arg2) => And(go(arg1, m), go(arg2, m))
      case Or(arg1, arg2) => Or(go(arg1, m), go(arg2, m))
      case All(v, arg) => quant(v, arg, m, All(_, _))
      case Ex(v, arg) => quant(v, arg, m, Ex(_, _))
      case Prev(i, arg) => Prev(i, go(arg, m))
      case Next(i, arg) => Next(i, go(arg, m))
      case Since(i, arg1, arg2) => Since(i, go(arg1, m), go(arg2, m))
      case Trigger(i, arg1, arg2) => Trigger(i, go(arg1, m), go(arg2, m))
      case Until(i, arg1, arg2) => Until(i, go(arg1, m), go(arg2, m))
      case Release(i, arg1, arg2) => Release(i, go(arg1, m), go(arg2, m))
      case errf @ _ => throw new UnsupportedOperationException(s"Operator not supported in the QTL translation: ${errf}")
    }
    go(phi, m)
  }

  private def substitutePred(phi: GenFormula[String], name: String, params: Seq[String],
                             body: GenFormula[String]): GenFormula[String] = phi match {
    case Pred(r, args @ _*) if r == name && args.length == params.length =>
      substituteVars(body, params.zip(args).toMap)
    case True() | False() | Rel(_, _, _) | Pred(_, _*) => phi
    case Not(arg) => Not(substitutePred(arg, name, params, body))
    case And(arg1, arg2) => And(substitutePred(arg1, name, params, body), substitutePred(arg2, name, params, body))
    case Or(arg1, arg2) => Or(substitutePred(arg1, name, params, body), substitutePred(arg2, name, params, body))
    case All(v, arg) => All(v, substitutePred(arg, name, params, body))
    case Ex(v, arg) => Ex(v, substitutePred(arg, name, params, body))
    case Prev(i, arg) => Prev(i, substitutePred(arg, name, params, body))
    case Next(i, arg) => Next(i, substitutePred(arg, name, params, body))
    case Since(i, arg1, arg2) => Since(i, substitutePred(arg1, name, params, body), substitutePred(arg2, name, params, body))
    case Trigger(i, arg1, arg2) => Trigger(i, substitutePred(arg1, name, params, body), substitutePred(arg2, name, params, body))
    case Until(i, arg1, arg2) => Until(i, substitutePred(arg1, name, params, body), substitutePred(arg2, name, params, body))
    case Release(i, arg1, arg2) => Release(i, substitutePred(arg1, name, params, body), substitutePred(arg2, name, params, body))
    case errf @ _ => throw new UnsupportedOperationException(s"Operator not supported in the QTL translation: ${errf}")
  }

  /** Eliminates LET definitions by substituting their bodies at the use sites. */
  def expandLets(phi: GenFormula[String]): GenFormula[String] = phi match {
    case Let(p, f, g) =>
      val params = p.args.map {
        case Var(v) => v
        case t => throw new UnsupportedOperationException(s"LET head parameters must be variables, found: ${t}")
      }
      if (params.distinct.length != params.length)
        throw new UnsupportedOperationException(s"LET head parameters must be distinct: ${p}")
      substitutePred(expandLets(g), p.relation, params, expandLets(f))
    case True() | False() | Rel(_, _, _) | Pred(_, _*) => phi
    case Not(arg) => Not(expandLets(arg))
    case And(arg1, arg2) => And(expandLets(arg1), expandLets(arg2))
    case Or(arg1, arg2) => Or(expandLets(arg1), expandLets(arg2))
    case All(v, arg) => All(v, expandLets(arg))
    case Ex(v, arg) => Ex(v, expandLets(arg))
    case Prev(i, arg) => Prev(i, expandLets(arg))
    case Next(i, arg) => Next(i, expandLets(arg))
    case Since(i, arg1, arg2) => Since(i, expandLets(arg1), expandLets(arg2))
    case Trigger(i, arg1, arg2) => Trigger(i, expandLets(arg1), expandLets(arg2))
    case Until(i, arg1, arg2) => Until(i, expandLets(arg1), expandLets(arg2))
    case Release(i, arg1, arg2) => Release(i, expandLets(arg1), expandLets(arg2))
    case errf @ _ => throw new UnsupportedOperationException(s"Operator not supported in the QTL translation: ${errf}")
  }

  /** Renames bound variables so that no name is bound twice or shadows a free variable;
    * DejaVu rejects duplicate quantifier names. */
  def uniquifyBoundVariables(phi: GenFormula[String]): GenFormula[String] = {
    val used = scala.collection.mutable.Set[String](phi.freeVariables.toSeq:_*)
    def fresh(hint: String): String = {
      val name = freshAvoiding(hint, used.toSet)
      used += name
      name
    }
    def go(f: GenFormula[String], env: Map[String, String]): GenFormula[String] = {
      def sub(t: Term[String]): Term[String] = substituteTerm(t, env.mapValues(Var[String](_)).toMap)
      f match {
        case True() | False() => f
        case Rel(op, t1, t2) => Rel(op, sub(t1), sub(t2))
        case Pred(r, args @ _*) => Pred(r, args.map(sub):_*)
        case Not(arg) => Not(go(arg, env))
        case And(arg1, arg2) => And(go(arg1, env), go(arg2, env))
        case Or(arg1, arg2) => Or(go(arg1, env), go(arg2, env))
        case All(v, arg) => { val nv = fresh(v); All(nv, go(arg, env + (v -> nv))) }
        case Ex(v, arg) => { val nv = fresh(v); Ex(nv, go(arg, env + (v -> nv))) }
        case Prev(i, arg) => Prev(i, go(arg, env))
        case Next(i, arg) => Next(i, go(arg, env))
        case Since(i, arg1, arg2) => Since(i, go(arg1, env), go(arg2, env))
        case Trigger(i, arg1, arg2) => Trigger(i, go(arg1, env), go(arg2, env))
        case Until(i, arg1, arg2) => Until(i, go(arg1, env), go(arg2, env))
        case Release(i, arg1, arg2) => Release(i, go(arg1, env), go(arg2, env))
        case errf @ _ => throw new UnsupportedOperationException(s"Operator not supported in the QTL translation: ${errf}")
      }
    }
    go(phi, Map.empty)
  }

  def explode[V](pred: Pred[V],inst:Iterable[Pred[V]]):Iterable[Pred[V]] = {
    inst.map{
      ip => {
        assert(ip.args.length == pred.args.length)
        val map: Map[Term[V],Term[V]] = pred.args.zip(ip.args)(collection.breakOut)
        Pred[V](pred.relation,pred.args.map{
          case Const(a) => Const[V](a)
          case v => map.getOrElse(v, v)
        }:_*)
      }
    }
  }

  def print(phi: GenFormula[VariableID[String]]): GenFormula[String] = {
    val freeVariables: Map[VariableID[String], String] = phi.freeVariables.map(v => (v, v.nameHint))(collection.breakOut)
    phi.map(new VariablePrinter(freeVariables))
  }

  def pushNegation[V](phi: GenFormula[V]): GenFormula[V] = {
    def pos(phi: GenFormula[V]): GenFormula[V] = phi match {
      case Not(arg) => neg(arg)
      case And(arg1, arg2) => And(pos(arg1), pos(arg2))
      case Or(arg1, arg2) => Or(pos(arg1), pos(arg2))
      case All(bound, arg) => All(bound, pos(arg))
      case Ex(bound, arg) => Ex(bound, pos(arg))
      case Prev(i, arg) => Prev(i, pos(arg))
      case Next(i, arg) => Next(i, pos(arg))
      case Since(i, arg1, arg2) => Since(i, pos(arg1), pos(arg2))
      case Trigger(i, arg1, arg2) => Trigger(i, pos(arg1), pos(arg2))
      case Until(i, arg1, arg2) => Until(i, pos(arg1), pos(arg2))
      case Release(i, arg1, arg2) => Release(i, pos(arg1), pos(arg2))
      case _ => phi
    }

    def neg(phi: GenFormula[V]): GenFormula[V] = phi match {
      case True() => False()
      case False() => True()
      case Not(arg) => pos(arg)
      case And(arg1, arg2) => Or(neg(arg1), neg(arg2))
      case Or(arg1, arg2) => And(neg(arg1), neg(arg2))
      case All(bound, arg) => Ex(bound, neg(arg))
      case Ex(bound, arg) => All(bound, neg(arg))
      case Prev(i, arg) => Or(Prev(i, neg(arg)), Not(Prev(i, True())))  // TODO(JS): Verify this equivalence
      case Next(i, arg) => Or(Next(i, neg(arg)), Not(Next(i, True())))  // TODO(JS): Verify this equivalence
      case Since(i, arg1, arg2) => Trigger(i, neg(arg1), neg(arg2))
      case Trigger(i, arg1, arg2) => Since(i, neg(arg1), neg(arg2))
      case Until(i, arg1, arg2) => Release(i, neg(arg1), neg(arg2))
      case Release(i, arg1, arg2) => Until(i, neg(arg1), neg(arg2))
      case _ => Not(pos(phi))
    }

    pos(phi)
  }

  def toParenthesizedQTL[V](sf:GenFormula[V]):String = sf match {
    case f @ And(_, _) => s"(${f.toQTL})" 
    case f @ Or(_, _) => s"(${f.toQTL})" 
    case f @ Since(_,_,_) => s"(${f.toQTL})"
    case _ => sf.toQTL
  }
}
