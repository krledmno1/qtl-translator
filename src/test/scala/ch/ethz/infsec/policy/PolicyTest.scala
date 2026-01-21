package ch.ethz.infsec.policy

import org.scalatest.EitherValues._
import org.scalatest.{FunSuite, Matchers}

class PolicyTest extends FunSuite with Matchers {
  import GenFormula._

  val Px = Pred("P", Var("x"))
  val Py = Pred("P", Var("y"))
  val Qxy = Pred("Q", Var("x"), Var("y"))
  val Qii: GenFormula[String] = Pred("Q", Const(7), Const(-42))
  val Qsx = Pred("Q", Const("foo"), Var("x"))
  val Eqxy = Pred("__eq", Var("x"), Var("y"))
  val Eqix = Pred("__eq", Const(-42), Var("x"))
  val Eqxi = Pred("__eq", Var("x"), Const(-42))
  val Eqixp = Pred("__eq", Const(42), Var("x"))
  val Eqxip = Pred("__eq", Var("x"), Const(42))
  val Lessxi = Pred("__less", Var("x"), Const(-123))
  val Lessix = Pred("__less", Const(-123), Var("x"))
  val Lessxip = Pred("__less", Var("x"), Const(123))
  val Lessixp = Pred("__less", Const(123), Var("x"))


  test("Atomic formulas should be parsed correctly") {
    Policy.parse("TRUE").right.value shouldBe True()
    Policy.parse("FALSE").right.value shouldBe False()
    Policy.parse("P()").right.value shouldBe Pred("P")
    Policy.parse("5_()").right.value shouldBe Pred("5_")
    Policy.parse("NOTX()").right.value shouldBe Pred("NOTX")
    Policy.parse("P(x)").right.value shouldBe Px
    Policy.parse("Q(x,y)").right.value shouldBe Qxy
    Policy.parse("Q(7, -42)").right.value shouldBe Qii
    Policy.parse("Q(\"foo\", x)").right.value shouldBe Qsx
    Policy.parse("((P(x)) )").right.value shouldBe Px
    Policy.parse("   P(\nx \t\r) ").right.value shouldBe Px
    Policy.parse("x=y").right.value shouldBe Eqxy
    Policy.parse("x = y").right.value shouldBe Eqxy
    Policy.parse("-42=x").right.value shouldBe Eqix
    Policy.parse("-42 = x").right.value shouldBe Eqix
    Policy.parse("x=-42").right.value shouldBe Eqxi
    Policy.parse("x = -42").right.value shouldBe Eqxi
    Policy.parse("42=x").right.value shouldBe Eqixp
    Policy.parse("42 = x").right.value shouldBe Eqixp
    Policy.parse("x=42").right.value shouldBe Eqxip
    Policy.parse("x = 42").right.value shouldBe Eqxip
    Policy.parse("x<-123").left should not be Nil //NOTE: this is not supported due to aggregations's "<-" token
    Policy.parse("x < -123").right.value shouldBe Lessxi
    Policy.parse("-123<x").right.value shouldBe Lessix
    Policy.parse("-123 < x").right.value shouldBe Lessix
    Policy.parse("x<123").right.value shouldBe Lessxip
    Policy.parse("x < 123").right.value shouldBe Lessxip
    Policy.parse("123<x").right.value shouldBe Lessixp
    Policy.parse("123 < x").right.value shouldBe Lessixp
    Policy.parse("x SUBSTRING \"foo\"").right.value shouldBe Pred(GenFormula.SUBSTRING, Var("x"), Const("foo"))
    Policy.parse("x MATCHES r\"foo\"").right.value shouldBe Pred(GenFormula.MATCHES, Var("x"), Const("foo"))
  }

  test("Propositional formulas should be parsed correctly") {
    Policy.parse("NOT P(x)").right.value shouldBe Not(Px)
    Policy.parse("P(x) OR FALSE").right.value shouldBe Or(Px, False())
    Policy.parse("P(x) OR P(y) OR FALSE").right.value shouldBe Or(Or(Px, Py), False())
    Policy.parse("P(x) AND P(y) AND FALSE").right.value shouldBe And(And(Px, Py), False())
    Policy.parse("(P(x) AND P(y)) OR NOT Q(x, y)").right.value shouldBe Or(And(Px, Py), Not(Qxy))
    Policy.parse("P(x) AND P(y) OR NOT Q(x, y)").right.value shouldBe Or(And(Px, Py), Not(Qxy))
    Policy.parse("P(x) AND (P(y) OR NOT Q(x, y))").right.value shouldBe And(Px, Or(Py, Not(Qxy)))
    Policy.parse("P(x) IMPLIES P(y) IMPLIES Q(x, y)").right.value shouldBe
      implies(Px, implies(Py, Qxy))
    Policy.parse("P(x) AND P(y) IMPLIES Q(7,-42) OR FALSE").right.value shouldBe
      implies(And(Px, Py), Or(Qii, False()))
    Policy.parse("P(x) EQUIV P(y) EQUIV Q(x, y)").right.value shouldBe
      equiv(equiv(Px, Py), Qxy)
    Policy.parse("P(x) EQUIV P(y) IMPLIES FALSE").right.value shouldBe
      equiv(Px, implies(Py, False()))
    Policy.parse("P(x) AND NOT x = y").right.value shouldBe And(Px, Not(Eqxy))
    Policy.parse("-42 = x IMPLIES -42 = x").right.value shouldBe
      implies(Eqix, Eqix)
  }

  test("First-order formulas should be parsed correctly") {
    Policy.parse("EXISTS x. P(x)").right.value shouldBe Ex("x", Px)
    Policy.parse("FORALL x. P(x)").right.value shouldBe All("x", Px)
    Policy.parse("EXISTS x, y. P(x)").right.value shouldBe Ex("x", Ex("y", Px))
    Policy.parse("FORALL x, y. P(x)").right.value shouldBe All("x", All("y", Px))
    Policy.parse("EXISTS x. EXISTS y. Q(x, y)").right.value shouldBe Ex("x", Ex("y", Qxy))
    Policy.parse("FORALL x. EXISTS y. Q(x, y)").right.value shouldBe All("x", Ex("y", Qxy))
    Policy.parse("EXISTS foo. P(x)").right.value shouldBe Ex("foo", Px)
    Policy.parse("EXISTS x. P(x) IMPLIES P(y)").right.value shouldBe Ex("x", implies(Px, Py))
    Policy.parse("P(x) AND (FORALL y. P(y))").right.value shouldBe And(Px, All("y", Py))
  }

  test("Intervals should be parsed correctly") {
    Policy.parse("PREVIOUS FALSE").right.value shouldBe Prev(Interval.any, False())
    Policy.parse("PREVIOUS [0,0] FALSE").right.value shouldBe Prev(Interval(0, Some(1)), False())
    Policy.parse("PREVIOUS [3,5) FALSE").right.value shouldBe Prev(Interval(3, Some(5)), False())
    Policy.parse("PREVIOUS [3,5] FALSE").right.value shouldBe Prev(Interval(3, Some(6)), False())
    Policy.parse("PREVIOUS (3,5) FALSE").right.value shouldBe Prev(Interval(4, Some(5)), False())
    Policy.parse("PREVIOUS [3,5) FALSE").right.value shouldBe Prev(Interval(3, Some(5)), False())
    Policy.parse("PREVIOUS [0,*) FALSE").right.value shouldBe Prev(Interval(0, None), False())
    Policy.parse("PREVIOUS [3,*] FALSE").right.value shouldBe Prev(Interval(3, None), False())
    Policy.parse("PREVIOUS [3s,5m) FALSE").right.value shouldBe Prev(Interval(3, Some(5 * 60)), False())
    Policy.parse("PREVIOUS [3h,5d) FALSE").right.value shouldBe
      Prev(Interval(3 * 60 * 60, Some(5 * 24 * 60 * 60)), False())
  }

  test("Temporal formulas should be parsed correctly") {
    Policy.parse("PREVIOUS [3,5) P(x)").right.value shouldBe Prev(Interval(3, Some(5)), Px)
    Policy.parse("NEXT [3,5) P(x)").right.value shouldBe Next(Interval(3, Some(5)), Px)
    Policy.parse("EVENTUALLY [3,5) P(x)").right.value shouldBe eventually(Interval(3, Some(5)), Px)
    Policy.parse("SOMETIMES [3,5) P(x)").right.value shouldBe eventually(Interval(3, Some(5)), Px)
    Policy.parse("ONCE [3,5) P(x)").right.value shouldBe once(Interval(3, Some(5)), Px)
    Policy.parse("ALWAYS [3,5) P(x)").right.value shouldBe always(Interval(3, Some(5)), Px)
    Policy.parse("HISTORICALLY [3,5) P(x)").right.value shouldBe historically(Interval(3, Some(5)), Px)
    Policy.parse("PAST_ALWAYS [3,5) P(x)").right.value shouldBe historically(Interval(3, Some(5)), Px)
    Policy.parse("P(x) SINCE [3,5) P(y)").right.value shouldBe Since(Interval(3, Some(5)), Px, Py)
    Policy.parse("P(x) UNTIL [3,5) P(y)").right.value shouldBe Until(Interval(3, Some(5)), Px, Py)

    Policy.parse("P(x) SINCE [3,5) TRUE SINCE P(y)").right.value shouldBe
      Since(Interval(3, Some(5)), Px, Since(Interval.any, True(), Py))
    Policy.parse("P(x) AND P(y) UNTIL Q(x, y)").right.value shouldBe Until(Interval.any, And(Px, Py), Qxy)
    Policy.parse("EXISTS x. P(x) SINCE P(y)").right.value shouldBe Since(Interval.any, Ex("x", Px), Py)
    Policy.parse("P(x) IMPLIES ONCE Q(x, y)").right.value shouldBe
      implies(Px, once(Interval.any, Qxy))
    Policy.parse("P(x) IMPLIES ONCE Q(x,y) AND P(x)").right.value shouldBe
      implies(Px, once(Interval.any, And(Qxy, Px)))
    Policy.parse("NOT PREVIOUS ONCE P(x)").right.value shouldBe Not(Prev(Interval.any, once(Interval.any, Px)))

  }

  test("Aggregations should be parsed correctly") {
    Policy.parse("r <- CNT x Q(\"foo\", x)").right.value shouldBe Aggr(Var("r"), CNT(), Var("x"), Qsx, Seq())
    Policy.parse("r <- SUM x Q(\"foo\", x)").right.value shouldBe Aggr(Var("r"), SUM(), Var("x"), Qsx, Seq())
    Policy.parse("r <- AVG x Q(\"foo\", x)").right.value shouldBe Aggr(Var("r"), AVG(), Var("x"), Qsx, Seq())
    Policy.parse("r <- MIN x Q(\"foo\", x)").right.value shouldBe Aggr(Var("r"), MIN(), Var("x"), Qsx, Seq())
    Policy.parse("r <- MAX x Q(\"foo\", x)").right.value shouldBe Aggr(Var("r"), MAX(), Var("x"), Qsx, Seq())
    Policy.parse("r <- MED x Q(\"foo\", x)").right.value shouldBe Aggr(Var("r"), MED(), Var("x"), Qsx, Seq())
    Policy.parse("r <- CNT x;x Q(\"foo\", x)").right.value shouldBe Aggr(Var("r"), CNT(), Var("x"), Qsx, Seq(Var("x")))
    Policy.parse("r <- CNT x;x,y Q(x,y)").right.value shouldBe Aggr(Var("r"), CNT(), Var("x"), Qxy, Seq(Var("x"),Var("y")))
    Policy.parse("P() AND r <- CNT x;x Q(\"foo\", x)").right.value shouldBe And(Pred("P"),Aggr(Var("r"), CNT(), Var("x"), Qsx, Seq(Var("x"))))
    Policy.parse("(r <- CNT x;x Q(\"foo\", x)) AND P()").right.value shouldBe And(Aggr(Var("r"), CNT(), Var("x"), Qsx, Seq(Var("x"))),Pred("P"))
    Policy.parse("r <- CNT x;x Q(\"foo\", x) AND P()").right.value shouldBe Aggr(Var("r"), CNT(), Var("x"), And(Qsx,Pred("P")), Seq(Var("x")))
    Policy.parse("r <- CNT x ONCE P()").right.value shouldBe Aggr(Var("r"), CNT(), Var("x"), once(arg = Pred("P")), Seq())
    Policy.parse("r <- CNT x;z Q(x,y,z)").right.value shouldBe Aggr(Var("r"), CNT(), Var("x"), Pred("Q", Var("x"), Var("y"), Var("z")), Seq(Var("z")))
  }

  test("Let should be parsed correctly") {
    val x = Var("x")
    val y = Var("y")
    val px = Pred("p", x)
    val qy = Pred("q", y)
    val rx = Pred("r", x)

    Policy.parse("LET r(x) = p(x) IN r(x)").right.value shouldBe Let(rx, px, rx)
    Policy.parse("LET r(x) = p(x) IN q(y) AND r(x)").right.value shouldBe Let(rx, px, And(qy, rx))
    Policy.parse("LET r(x) = p(x) AND EXISTS y. q(y) IN r(x)").right.value shouldBe Let(rx, And(px, Ex("y", qy)), rx)
    Policy.parse("LET r(x) = r(x) IN r(x)").right.value shouldBe Let(rx, rx, rx)
    Policy.parse("LET r(x) = p(x) IN LET p(x) = r(x) IN p(x)").right.value shouldBe Let(rx, px, Let(px, rx, px))
    Policy.parse("LET p(x) = LET p(x) = r(x) IN p(x) IN p(x)").right.value shouldBe Let(px, Let(px, rx, px), px)
    Policy.parse("LET p(x) = NOT p(x) SINCE r(x) IN p(x)").right.value shouldBe Let(px,Since(Interval.any,Not(px),rx),px)

  }

  test("Complex formula should be parsed correctly") {

    val s = Var("s");
    val id = Var("id")
    val a1 = Var("a1")
    val a2 = Var("a2")
    val a3 = Var("a3")
    val a4 = Var("a4")
    val pn = Var("pn")
    val r = Var("r")
    val dep = Var("dep")
    val c = Var("c")
    val t = Var("t")
    val ratio = Var("ratio")
    val rej = Var("rej")
    val req = Var("req")


    def chro(x:Term[String],y:Term[String],z:Term[String]):Pred[String] = Pred("chro",id,a1,x,y,z,Var("r"))


    Policy.parse(
      "LET c_reject(id) = EXISTS a1, s, a3, a4, r. chro(id, a1, s, a3, a4, r) AND (s = 5 OR s = 19)  IN " +
      "LET c_accept(id) = EXISTS a1, s, a3, a4, r. chro(id, a1, 25, a3, a4, r) IN " +
      "LET c_first_person(id, pn) = EXISTS a1, a3, r. chro(id, a1, 1, a3, pn, r) IN " +
      "LET person_of_department(pn, dep) = EXISTS a1, a2. ONCE pers(pn, a1, a2, dep) IN " +
      "LET first_department(id, dep) = EXISTS pn. c_first_person(id, pn) AND person_of_department(pn, dep) IN " +
      "LET rejected_department(id, dep) = c_reject(id) AND ONCE first_department(id, dep) IN " +
      "LET count_rejections(c, dep) = c <- CNT id; dep ONCE rejected_department(id, dep) IN " +
      "LET count_requests(c, dep) = c <- CNT t; dep ONCE tp(t) AND EXISTS id. first_department(id, dep) IN " +
      "LET result(ratio, req, rej, dep) = count_rejections(rej, dep) AND count_requests(req, dep) AND ratio = i2f(rej) / i2f(req) IN " +
      "LET last() = NEXT EXISTS t. ts(t) AND t > 10000000000.0 IN " +
        "last() AND result(a, b, c, d)").right.value shouldBe
      Let[String](Pred("c_reject",id),
        ex(Seq(a1,s,a3,a4,r),And(chro(s,a3,a4),Or(eql(s,Const(5)),eql(s,Const(19))))),
        Let(Pred("c_accept",id),
          ex(Seq(a1,s,a3,a4,r),chro(Const(25),a3,a4)),
          Let(Pred("c_first_person",id,pn),
            ex(Seq(a1,a3,r),chro(Const(1),a3,pn)),
            Let(Pred("person_of_department",pn,dep),
              ex(Seq(a1,a2), once(Interval.any, Pred("pers",pn,a1,a2,dep))),
              Let(Pred("first_department",id,dep),
                Ex(pn.variable,And(Pred("c_first_person",id,pn),Pred("person_of_department",pn,dep))),
                Let(Pred("rejected_department",id,dep),
                  And(Pred("c_reject",id),once(Interval.any,Pred("first_department",id,dep))),
                  Let(Pred("count_rejections",c,dep),
                    Aggr(c,CNT(),id,once(Interval.any,Pred("rejected_department",id,dep)),Seq(dep)),
                    Let(Pred("count_requests",c,dep),
                      Aggr(c,CNT(),t,once(Interval.any,And(Pred("tp",t),Ex(id.variable,Pred("first_department",id,dep)))),Seq(dep)),
                      Let(Pred("result",ratio,req,rej,dep),
                        And(And(Pred("count_rejections",rej,dep),Pred("count_requests",req,dep)),eql(ratio,div(i2f(rej),i2f(req)))),
                        Let(Pred("last"),
                          Next(Interval.any,Ex(t.variable,And(Pred("ts",t),gte(t,Const(10000000000.0))))),
                          And(Pred("last"),Pred("result",Var("a"),Var("b"),Var("c"),Var("d")))))))))))))
  }

  test("Unary operator following NOT must not be confused with a predicate") {
    Policy.parse("NOT PREVIOUS (P(x))") should be ('right)
  }


  // test("Printing QTL formulas should be correct") {
  //   val policyText =
  //     "EXISTS x. P(x)".stripMargin

  //   val expectedQTL =
  //     "prop a: Exists x. P(x)".stripMargin

  //   val formula = Policy.parse(policyText).right.value
  //   val qtlString = formula.toQTLString(negated = false)

  //   qtlString shouldBe expectedQTL
  // }


}
