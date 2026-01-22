package ch.ethz.infsec.policy

import fastparse.{WhitespaceApi, all, noApi}
import fastparse.noApi._

private object PolicyParsers {

  private type FormulaS = GenFormula[String]

  private object Token {
    import fastparse.all._

    val Comment: P0 = P( "(*" ~/ (!"*)" ~ AnyChar).rep ~/ "*)" )
    val LineComment: P0 = P( "#" ~/ CharsWhile(c => c != '\n' && c != '\r'))
    val Whitespace: P0 = P( NoTrace((CharsWhileIn(" \t\n\r") | Comment | LineComment).rep) )

    val Letter: P0 = P( CharIn('a' to 'z', 'A' to 'Z') )
    val Digit: P0 = P( CharIn('0' to '9') )
    val AnyStringExclQuotes: P0 = P( (Letter | Digit | CharIn("_-/:")).rep )
    val NonDigit: P0 = P( Letter | CharIn("_-/:\'\"") )
    val AnyString: P0 = P( (NonDigit | Digit).rep )

    val Identifier: P[String] = P( ((Letter | Digit | "_") ~ AnyString).! )

    val Integer: P[Long] = P( ("-".? ~ Digit.rep(min = 1) ~ !NonDigit).!.map(_.toLong) )
    // TODO(JS): Should use an exact type for rationals.
    val Rational: P[Double] = P( ("-".? ~ Digit.rep(min = 1) ~ "." ~/ Digit.rep(min = 1) ~ !NonDigit).!.map(_.toDouble) )
    val QuotedString: P[String] = P(
      "\"" ~/ ((CharPred(c => c != '"' && c != '\\') | "\\" ~/ AnyChar).rep).! ~/ "\""
    )
    val RegexpLiteral: P[String] = P("r" ~ QuotedString)

    val Quantity: P[(Int, String)] = P( Digit.rep(min = 1).!.map(_.toInt) ~/ Letter.?.! )

    def keyword(word: String): P0 = P( word ~ !(NonDigit | Digit) )(sourcecode.Name(s"`$word`"))

    //Eagerly matched (they cannot be parts of an identifier)
    def operator(word: String): P0 = P( word ~ (!NonDigit | !Digit) )(sourcecode.Name(s"`$word`"))


    val Eventually: P0 = P( keyword("EVENTUALLY") | keyword("SOMETIMES") )
    val Once: P0 = P( keyword("ONCE") )
    val Always: P0 = P( keyword("ALWAYS") )
    val Historically: P0 = P( keyword("PAST_ALWAYS") | keyword("HISTORICALLY") )
    val SinceUntil: P0 = P( keyword("SINCE") | keyword("UNTIL") )

    val CNT: P0 = P(keyword("CNT"))
    val SUM: P0 = P(keyword("SUM"))
    val AVG: P0 = P(keyword("AVG"))
    val MIN: P0 = P(keyword("MIN"))
    val MAX: P0 = P(keyword("MAX"))
    val MED: P0 = P(keyword("MED"))

    val Arrow: P0 = P(operator("<-"))
    val Equals: P0 = P(operator("="))
    val Less: P0 = P(operator("<") ~ !"-" ~ !"=")
    val Greater: P0 = P(operator(">") ~ !"-" ~ !"=")
    val LessEq: P0 = P(operator("<="))
    val GreaterEq: P0 = P(operator(">="))

    val Plus: P0 = P(operator("+"))
    val Minus: P0 = P(operator("-"))
    val Times: P0 = P(operator("*"))
    val Div: P0 = P(operator("/"))
    val Mod: P0 = P(keyword("MOD"))
    val F2I: P0 = P(keyword("f2i"))
    val I2F: P0 = P(keyword("i2f"))
  }

  private val WhitespaceWrapper = WhitespaceApi.Wrapper(Token.Whitespace)
  import WhitespaceWrapper._

  private def timeUnit(unit: String): Int = unit match {
    case "d" => 24 * 60 * 60
    case "h" => 60 * 60
    case "m" => 60
    case "s" | "" => 1
    case _ => throw new RuntimeException(s"unrecognized time unit: $unit")  // TODO(JS): Proper error handling
  }

  private def optionalInterval(spec: Option[Interval]): Interval = spec.getOrElse(Interval.any)

  private def leftAssocTerm[T](op: P[(T, T) => T], sub: P[T]): P[T] =
    (sub ~ (op ~ sub).rep).map(xs => {
      xs._2.foldLeft(xs._1){
        (acc, f) => f._1(acc,f._2)
      }
    })

  private def leftAssoc[T](op: P0, sub: P[T], subp: P[T], mk: (T, T) => T): P[T] =
    (sub.rep(min = 1, sep = op) ~ (op ~ subp).?).map(xs => {
      val xs2 = xs._1 ++ xs._2
      xs2.tail.foldLeft(xs2.head)(mk)
    })

  private def rightAssoc(op: P0, sub: P[FormulaS], subp: P[FormulaS], mk: (FormulaS, FormulaS) => FormulaS): P[FormulaS] =
    (sub.rep(min = 1, sep = op) ~ (op ~ subp).?).map(xs => {
      val xs2 = xs._1 ++ xs._2
      xs2.init.foldRight(xs2.last)(mk)
    })

  private  def rightAssocLet(let: P0, sub: P[FormulaS], in: P0, subp: P[FormulaS], mk: (Pred[String], FormulaS, FormulaS) => FormulaS): P[FormulaS] =
    ((let ~/ Predicate ~/ Token.Equals ~/ sub ~/ in).rep(min=1) ~ subp).map( xs => {
      xs._1.foldRight(xs._2){(f,l) =>  mk(f._1,f._2,l)}
    })


  private def quantifier(op: P0, sub: P[FormulaS], mk: (String, FormulaS) => FormulaS): P[FormulaS] =
    (op ~/ Token.Identifier.rep(min = 1, sep = ",") ~ "." ~/ sub).map { case (vars, phi) =>
      vars.init.foldRight(mk(vars.last, phi))(mk)
    }

  private def aggregate(sub: P[FormulaS], mk: (Var[String], AggregateFunction, Var[String], FormulaS, Seq[Var[String]]) => FormulaS): P[FormulaS] =
    (Variable ~ Token.Arrow ~/ AggFunc ~/ Variable ~/ (";" ~ Variable.rep(min = 1, sep=",")).? ~/ sub ).map{
      case (r, agg, x, gs, f) =>  gs match {
        case None => mk(r, agg, x, f, Seq())
        case Some(vs) => mk(r, agg, x, f, vs)
      }
    }

  private def unaryTemporal(op: P0, sub: P[FormulaS], mk: (Interval, FormulaS) => FormulaS): P[FormulaS] =
    (op ~/ TimeInterval.? ~/ sub).map{ case (i, phi) => mk(optionalInterval(i), phi) }

  // TODO(JS): Support decimal numbers
  // TODO(JS): Treat regexp literals as a different type
  val Constant: P[Const[String]] = P(
    Token.Rational.map(Const[String](_)) | Token.Integer.map(Const[String](_)) |
    Token.QuotedString.map(Const[String](_)) | Token.RegexpLiteral.map(Const[String](_))
  )
  val Variable: P[Var[String]] = P(
    Token.Identifier.map(Var(_))
  )
//  val ApplyFunc: P[Apply[String]] = P(
//    ApplyFunc1 | ApplyFunc2
//  )

  val ApplyFunc1: P[Apply1[String]]= P(
    (Token.F2I ~/ "(" ~/ Term ~/ ")").map(x => Apply1(F2I(),x)) |
      (Token.I2F ~/ "(" ~/ Term ~/ ")").map(x => Apply1(I2F(),x))
  )

  val mkplus: (Term[String], Term[String]) => Term[String] = Apply2[String](PLUS(),_,_)
  val mkminus:(Term[String], Term[String]) => Term[String] = Apply2[String](MINUS(),_,_)
  val mktimes:(Term[String], Term[String]) => Term[String] = Apply2[String](TIMES(),_,_)
  val mkdiv:  (Term[String], Term[String]) => Term[String] = Apply2[String](DIV(),_,_)
  val mkmod:  (Term[String], Term[String]) => Term[String] = Apply2[String](MOD(),_,_)


  val Term2: P[Term[String]] = P(
    "(" ~/ Term ~/ ")" | ApplyFunc1 | Constant | Variable
  )

  val Term1: P[Term[String]] = P(
    leftAssocTerm[Term[String]](Token.Times.map{_ => mktimes} |
                                Token.Div.map{_ => mkdiv}|
                                Token.Mod.map{_ => mkmod},Term2)
  )

  val Term: P[Term[String]]= P(
    leftAssocTerm[Term[String]](Token.Plus.map{_ => mkplus} |
                                Token.Minus.map{_ => mkminus},Term1)
  )

  val AggFunc: P[AggregateFunction] = P(
    Token.CNT.map(_ => CNT()) |
    Token.SUM.map(_ => SUM()) |
    Token.AVG.map(_ => AVG()) |
    Token.MIN.map(_ => MIN()) |
    Token.MAX.map(_ => MAX()) |
    Token.MED.map(_ => MED())
  )

  val TimeInterval: P[Interval] = P( (("(" | "[").! ~ Token.Quantity ~ "," ~
    ("*" ~ PassWith(None) | Token.Quantity.map(Some(_))) ~ (")" | "]").!)
    .map{ case (lk, (lb, lu), rbo, rk) =>
      val leftBound = lb * timeUnit(lu) + (if (lk == "(") 1 else 0)
      val rightBound = rbo.map{ case (rb, ru) => rb * timeUnit(ru) + (if (rk == "]") 1 else 0) }
      Interval(leftBound, rightBound)
    }
  )

  val Predicate: P[Pred[String]] = P(
    (Token.Identifier ~ "(" ~/ Term.rep(sep = ",") ~ ")").map(x => Pred(x._1, x._2:_*))
  )

  val Formula9: P[FormulaS] = P(
    ("(" ~/ Formula0 ~/ ")") |
    Token.keyword("TRUE") ~/ PassWith(True[String]()) |
    Token.keyword("FALSE") ~/ PassWith(False[String]()) |
    (Token.keyword("NOT") ~/ (Formula2Prefix | Formula9)).map(Not(_)) |
    Predicate |
    (Term ~ Token.Equals ~/ Term).map(x => GenFormula.eql(x._1, x._2)) |
    (Term ~ Token.Less ~/ Term).map(x => GenFormula.lte(x._1, x._2)) |
    (Term ~ Token.LessEq ~/ Term).map(x => GenFormula.leq(x._1, x._2)) |
    (Term ~ Token.Greater ~/ Term).map(x => GenFormula.gte(x._1, x._2)) |
    (Term ~ Token.GreaterEq ~/ Term).map(x => GenFormula.geq(x._1, x._2)) |
    (Term ~ Token.keyword("SUBSTRING") ~/ Term).map(x => GenFormula.substr(x._1, x._2)) |
    (Term ~ Token.keyword("MATCHES") ~/ Term).map(x => GenFormula.matches(x._1, x._2))
  )

  val Formula8: P[FormulaS] = P( leftAssoc[FormulaS](Token.keyword("AND"), Formula9, Formula2Prefix, And(_, _)) )

  val Formula7: P[FormulaS] = P( leftAssoc[FormulaS](Token.keyword("OR"), Formula8, Formula2Prefix, Or(_, _)) )

  val Formula6: P[FormulaS] = P( rightAssoc(Token.keyword("IMPLIES"), Formula7, Formula2Prefix, GenFormula.implies) )

  val Formula5: P[FormulaS] = P( leftAssoc[FormulaS](Token.keyword("EQUIV"), Formula6, Formula2Prefix, GenFormula.equiv) )



  val Formula2Prefix: P[FormulaS] = P(
    unaryTemporal(Token.keyword("PREVIOUS"), Formula2, Prev(_, _)) |
    unaryTemporal(Token.keyword("NEXT"), Formula2, Next(_, _)) |
    unaryTemporal(Token.Eventually, Formula2, GenFormula.eventually) |
    unaryTemporal(Token.Once, Formula2, GenFormula.once) |
    unaryTemporal(Token.Always, Formula2, GenFormula.always) |
    unaryTemporal(Token.Historically, Formula2, GenFormula.historically) |
    quantifier(Token.keyword("EXISTS"), Formula2, Ex(_, _)) |
    quantifier(Token.keyword("FORALL"), Formula2, All(_, _)) |
    aggregate(Formula2,Aggr(_,_,_,_,_))
  )

  val Formula2: P[FormulaS] = P( Formula2Prefix | Formula5 )

  val Formula1: P[FormulaS] = P(
    (Formula2 ~ ( Token.SinceUntil.! ~/ TimeInterval.? ~/ Formula2).rep)
      .map{ case (phi1, ops) =>
        ops.foldRight(identity[FormulaS](_)){ case ((op, i, phi), mkr) => lhs =>
          val rhs = mkr(phi)
          val interval = optionalInterval(i)
          op match {
            case "SINCE" => Since(interval, lhs, rhs)
            case "UNTIL" => Until(interval, lhs, rhs)
          }
        }(phi1)
      }
  )

  val Formula0: P[FormulaS] = P( rightAssocLet(Token.keyword("LET"), Formula0, Token.keyword("IN"), Formula1, Let(_,_,_)) | Formula1 )

  val Policy: P[FormulaS] = P( Token.Whitespace ~ Formula0 ~ Token.Whitespace ~ End )
  val PolicyTerm: P[Term[String]] = P( Token.Whitespace ~ Term ~ Token.Whitespace ~ End )
  val PolicyConst: P[Term[String]] = P( Token.Whitespace ~ Constant ~ Token.Whitespace ~ End )

}

object Policy {
  def parse(input: String): Either[String, GenFormula[String]] = PolicyParsers.Policy.parse(input) match {
    case Parsed.Success(formula, _) => Right(formula)
    case Parsed.Failure(_, index, extra) =>
      val input = extra.input
      val trace = extra.traced
      Left(s"syntax error near ${input.repr.prettyIndex(input, index)}, due to ${trace}")
  }

  def parseTerm(input: String): Either[String, Term[String]] = PolicyParsers.PolicyTerm.parse(input) match {
    case Parsed.Success(term, _) => Right(term)
    case Parsed.Failure(_, index, extra) =>
      val input = extra.input
      val trace = extra.traced
      Left(s"syntax error near ${input.repr.prettyIndex(input, index)}, due to ${trace}")
  }
  def parseConst(input: String): Either[String, Term[String]] = PolicyParsers.PolicyConst.parse(input) match {
    case Parsed.Success(term, _) => Right(term)
    case Parsed.Failure(_, index, extra) =>
      val input = extra.input
      val trace = extra.traced
      Left(s"syntax error near ${input.repr.prettyIndex(input, index)}, due to ${trace}")
  }

  def read(input: String): Either[String, Formula] =
    parse(input).right.flatMap { rawFormula =>
      rawFormula.intervalCheck match {
        case Nil => Right(GenFormula.resolve(rawFormula))
        case error1 :: _ => Left(error1)
      }
    }
}
