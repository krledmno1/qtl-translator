package ch.ethz.infsec.policy

import ch.ethz.infsec.monitor.DataType
import ch.ethz.infsec.policy.GenFormula.Signature

import java.util.concurrent.atomic.AtomicInteger
import scala.annotation.tailrec


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
  override def toQTL: String = toString
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
  override def toQTL: String = throw new NotImplementedError("Functional terms in QTL")
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
  override def toQTL: String = throw new NotImplementedError("Functional terms in QTL")
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
  def toQTL:String = if (this.equals(Interval.any)) "" else throw new UnsupportedOperationException
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
  def close(neg:Boolean): GenFormula[V] = {
    def closeFormula(fma:GenFormula[V],vars:List[V]):GenFormula[V] = vars match {
      case Nil => fma
      case v::vs => closeFormula(if (neg) Ex(v,fma) else All(v,fma) ,vs)
    }
    closeFormula(this, freeVariables.toList)
  }

  def freeVariableTypes(signature: Signature): Map[V, DataType] = {
    val typing = inferTypes(signature).table
    freeVariables.map(v => typing(v).inspect match {
      case Left(_) => throw new Exception("Variable " + v + " is polymorphic")
      case Right(t) => v -> t
    }).toMap
  }

  def translateToQTL(epred: Pred[String]): (GenFormula[String], Map[Pred[String],GenFormula[String]]) = {
    val phi = this.asInstanceOf[GenFormula[String]]
    def predsToLets(phi: GenFormula[String], lets: Map[Pred[String],GenFormula[String]]): Map[Pred[String],GenFormula[String]] = phi match {
      case True() => lets
      case False() => lets
      case p @ Pred(pn, args @ _*) => {
        val newpred = "_" + pn
        for (p <- lets.keys) {
          if (p.relation == newpred)
            if (p.args.toList != args.toList)
              throw new UnsupportedOperationException(s"Error: Predicate ${pn} used with different arguments in the formula, which is not supported in QTL" )
            else
              return lets
        }
        val pred = Pred(newpred, args:_*)
        val let = And(epred, Prev(Interval.any, Since(Interval.any,Not(epred),p))) 
        lets + (pred -> let)
      }
      case Not(arg) => predsToLets(arg, lets)
      case And(arg1, arg2) => {
        val map = predsToLets(arg1, lets) 
        predsToLets(arg2, map)
      }
      case Or(arg1, arg2) => {
        val map = predsToLets(arg1, lets) 
        predsToLets(arg2, map)
      }
      case All(_, arg) => predsToLets(arg, lets)
      case Ex(_, arg) => predsToLets(arg, lets)
      case Prev(_, arg) => predsToLets(arg, lets)
      case Next(_, arg) => predsToLets(arg, lets)
      case Since(_, arg1, arg2) => {
        val map = predsToLets(arg1, lets)
        predsToLets(arg2, map)
      }
      case Trigger(_, arg1, arg2) => {
        val map = predsToLets(arg1, lets)
        predsToLets(arg2, map)
      }
      case Until(_, arg1, arg2) => {
        val map = predsToLets(arg1, lets)
        predsToLets(arg2, map)
      }
      case Release(_, arg1, arg2) => {
        val map = predsToLets(arg1, lets)
        predsToLets(arg2, map)
      }
      case Let(_, f, g) => {
        val map = predsToLets(f, lets)
        predsToLets(g, map)
      }
    }

    val letsMap = predsToLets(phi, Map.empty)

    def rho(f: GenFormula[String]): GenFormula[String] = f match {
      case True() => True()
      case False() => False()
      case Pred(relation, args @ _*) => Pred("_"+relation, args:_*)
      case Not(arg) => Not(rho(arg))
      case And(arg1, arg2) => And(rho(arg1), rho(arg2))
      case Or(arg1, arg2) => Or(rho(arg1), rho(arg2))
      case All(bound, arg) => All(bound, rho(arg))
      case Ex(bound, arg) => Ex(bound, rho(arg))
      case Prev(i, arg) => Prev(i, rho(arg))
      case Since(i, arg1, arg2) => And(Since(i, Or(rho(arg1), Not(epred)), rho(arg2)), epred)
      case Let(p, f, g) => Let(p, rho(f), rho(g))
      case _ => throw new NotImplementedError("Rho transformation not implemented for this formula type")
    }

    def extractLets(f: GenFormula[String]): (GenFormula[String], Map[Pred[String],GenFormula[String]]) = f match {
      case True() => (True(), Map.empty)
      case False() => (False(), Map.empty)
      case p @ Pred(_, _*) => (p, Map.empty)
      case Not(arg) => {
        val (rarg, lets) = extractLets(arg)
        (Not(rarg), lets)
      }
      case And(arg1, arg2) => {
        val (rarg1, lets1) = extractLets(arg1)
        val (rarg2, lets2) = extractLets(arg2)
        (And(rarg1, rarg2), lets1 ++ lets2)
      }
      case Or(arg1, arg2) => {
        val (rarg1, lets1) = extractLets(arg1)
        val (rarg2, lets2) = extractLets(arg2)
        (Or(rarg1, rarg2), lets1 ++ lets2)
      }
      case All(bound, arg) => {
        val (rarg, lets) = extractLets(arg)
        (All(bound, rarg), lets)
      }
      case Ex(bound, arg) => {
        val (rarg, lets) = extractLets(arg)
        (Ex(bound, rarg), lets)
      }
      case Prev(i, arg) => {
        val (rarg, lets) = extractLets(arg)
        (Prev(i, rarg), lets)
      }
      case Since(i, arg1, arg2) => {
        val (rarg1, lets1) = extractLets(arg1)
        val (rarg2, lets2) = extractLets(arg2)
        (Since(i, rarg1, rarg2), lets1 ++ lets2)
      }
      case Let(p, f, g) => {
        val (rg, letsG) = extractLets(g)
        (rg, letsG + (p -> f))
      }
      case _ => throw new NotImplementedError("Extract let is not implemented for this formula type")
    }
  

    val (phi1,lets) = extractLets(phi)

    (rho(phi1), lets++letsMap)

    // letsMap.values.foldRight(rho(phi)) {
    //   (let, acc) => let(acc)
    // }
  }

  def toQTLString(neg:Boolean, epred: Pred[String]):String = {
    val (fma,lets) = this.translateToQTL(epred)
    val closed = fma.close(neg)
    val f = if (neg) Not(closed) else closed
    "prop fma: " + f.toQTL + " where " + 
      lets.map{ case (p, body) => s"${p.toString} := ${body.toQTL}"}.mkString(", ")
  }
  def toQTL:String
}

//sealed trait Operator{
//  val op:String
//  override def toString:String = s" $op "
//}
//case class EQ() extends Operator{
//  val op = "="
//}
//case class LT() extends Operator{
//  val op = "<"
//}
//case class LE() extends Operator{
//  val op = "<="
//}
//case class GT() extends Operator{
//  val op = ">"
//}
//case class GE() extends Operator{
//  val op = ">="
//}
//case class SUBSTRING() extends Operator{
//  val op = "SUBSTRING"
//}
//case class MATCHES() extends Operator{
//  val op = "MATCHES"
//}
//
//case class Rel[V](op:Operator, arg1: Term[V],arg2: Term[V]) extends GenFormula[V]{
//  override def atoms: Set[Pred[V]] = Set()
//  override def atomsInOrder: Seq[Pred[V]] = Seq()
//  override def freeVariables: Set[V] = arg1.freeVariables ++ arg2.freeVariables
//  override def freeVariablesInOrder: Seq[V] = arg1.freeVariablesInOrder ++ arg2.freeVariablesInOrder
//  override def map[W](mapper: VariableMapper[V, W]): GenFormula[W] = Rel(op,arg1.map(mapper),arg2.map(mapper))
//  override def intervalCheck: List[String] = Nil
//  override def toString: String = s"${arg1} ${op} ${arg2}"
//  override def toQTL: String = toString
//}

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

    // TODO(JS): Replace this hack with proper support for built-in relations.
    if (relation.startsWith("__")) {
      (ttys.toList, relation) match {
        case (ty1 :: ty2 :: Nil, GenFormula.EQ) => ty1.unify(ty2)
        case (ty1 :: ty2 :: Nil, GenFormula.SUBSTRING) =>
          ty1.unify(TypeSymbol.const(DataType.STRING))
          ty2.unify(TypeSymbol.const(DataType.STRING))
        case (ty1 :: ty2 :: Nil, GenFormula.MATCHES) =>
          ty1.unify(TypeSymbol.const(DataType.STRING))
          ty2.unify(TypeSymbol.const(DataType.STRING))
        case (ty1 :: ty2 :: Nil, _) => ty1.enforceNumeric().unify(ty2)
        case _ => throw new Exception("Wrong arity for predicate " + relation)
      }
    } else {
      for ((ty, cty) <- ttys zip signature((relation, args.length))) {
        ty.unify(TypeSymbol.const(cty))
      }
    }
    tc
  }

  override def map[W](mapper: VariableMapper[V, W]): Pred[W] = Pred(relation, args.map(_.map(mapper)):_*)
  override def intervalCheck: List[String] = Nil
  override def toString: String = s"$relation(${args.mkString(", ")})"
  override def toQTL: String = toString
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
  override def toQTL: String = s"! (${arg.toQTL})"
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
  override def toQTL: String = s"(${arg1.toQTL}) & (${arg2.toQTL})"
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
  override def toQTL: String = s"(${arg1.toQTL}) | (${arg2.toQTL})"
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
  override def toQTL: String = s"Forall ${Var(variable).toQTL}. (${arg.toQTL})"

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
  override def toQTL: String = s"Exists ${Var(variable).toQTL}. (${arg.toQTL})"

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
  override def toQTL: String = s"@ ${interval.toQTL} (${arg.toQTL})"
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
  override def toQTL: String = throw new UnsupportedOperationException
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
  override def toQTL: String = if (!arg1.equals(True[V]())) s"(${arg1.toQTL}) S ${interval.toQTL} (${arg2.toQTL})" else s"P ${interval.toQTL} (${arg2.toQTL})"
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
  override def toQTL: String = Not(Since(interval, Not(arg1), Not(arg1))).toQTL
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
  override def toQTL: String = throw new UnsupportedOperationException
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
  override def toQTL: String = Not(Since(interval, Not(arg1), Not(arg1))).toQTL
}

case class Let[V](p:Pred[V],f:GenFormula[V], g:GenFormula[V]) extends GenFormula[V]{
  require(p.freeVariables == f.freeVariables)

  private def explode(pred: Pred[V],inst:Iterable[Pred[V]]):Iterable[Pred[V]] = {
    inst.map{
      ip => {
        assert(ip.args.length == p.args.length)
        val map: Map[Term[V],Term[V]] = p.args.zip(ip.args)(collection.breakOut)
        Pred[V](pred.relation,pred.args.map{
          case Const(a) => Const[V](a)
          case v => map.getOrElse(v, v)
        }:_*)
      }
    }
  }
  override def atoms: Set[Pred[V]] = {
    val (inst, rest) = g.atoms.partition{ _.relation == p.relation}
    val repl = f.atoms.flatMap(explode(_,inst))
    repl union rest
  }
  override def atomsInOrder: Seq[Pred[V]] = {
    val (inst, rest) = g.atomsInOrder.partition{ _.relation == p.relation}
    val repl = f.atomsInOrder.flatMap(explode(_,inst.toIterable))
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
  override def toQTL: String = throw new NotImplementedError("Aggregations in QTL")
}

object GenFormula {
  type Signature = Map[(String, Int), Seq[DataType]]

  val EQ = "__eq"
  val LT = "__less"
  val LQ = "__less__eq"
  val GT = "__greater"
  val GQ = "__greater__eq"
  val SUBSTRING = "__substring"
  val MATCHES = "__matches"

  def implies[V](arg1: GenFormula[V], arg2: GenFormula[V]): GenFormula[V] = Or(Not(arg1), arg2)
  def equiv[V](arg1: GenFormula[V], arg2: GenFormula[V]): GenFormula[V] = And(implies(arg1, arg2), implies(arg2, arg1))
  def once[V](interval: Interval = Interval.any, arg: GenFormula[V]): GenFormula[V] = Since(interval, True(), arg)
  def historically[V](interval: Interval = Interval.any, arg: GenFormula[V]): GenFormula[V] = Trigger(interval, False(), arg)
  def eventually[V](interval: Interval = Interval.any, arg: GenFormula[V]): GenFormula[V] = Until(interval, True(), arg)
  def always[V](interval: Interval = Interval.any, arg: GenFormula[V]): GenFormula[V] = Release(interval, False(), arg)
  def ex[V](vs:Seq[Var[V]], arg:GenFormula[V]):GenFormula[V] = vs.foldRight(arg)((v,a) => Ex[V](v.variable,a))
  def all[V](vs:Seq[Var[V]], arg:GenFormula[V]):GenFormula[V] = vs.foldRight(arg)((v,a) => All[V](v.variable,a))
  def eql[V](t1:Term[V],t2:Term[V]):GenFormula[V] = Pred(EQ,t1,t2)
  def lte[V](t1:Term[V],t2:Term[V]):GenFormula[V] = Pred(LT,t1,t2)
  def leq[V](t1:Term[V],t2:Term[V]):GenFormula[V] = Pred(LQ,t1,t2)
  def gte[V](t1:Term[V],t2:Term[V]):GenFormula[V] = Pred(GT,t1,t2)
  def geq[V](t1:Term[V],t2:Term[V]):GenFormula[V] = Pred(GQ,t1,t2)

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

  
}
