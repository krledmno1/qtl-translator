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
  val Eqxy = Rel(EQ(), Var("x"), Var("y"))
  val Eqix = Rel(EQ(), Const(-42), Var("x"))
  val Eqxi = Rel(EQ(), Var("x"), Const(-42))
  val Eqixp = Rel(EQ(), Const(42), Var("x"))
  val Eqxip = Rel(EQ(), Var("x"), Const(42))
  val Lessxi = Rel(LT(), Var("x"), Const(-123))
  val Lessix = Rel(LT(), Const(-123), Var("x"))
  val Lessxip = Rel(LT(), Var("x"), Const(123))
  val Lessixp = Rel(LT(), Const(123), Var("x"))


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
    Policy.parse("x SUBSTRING \"foo\"").right.value shouldBe Rel(SUBSTRING(), Var("x"), Const("foo"))
    Policy.parse("x MATCHES r\"foo\"").right.value shouldBe Rel(MATCHES(), Var("x"), Const("foo"))
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


  test("Printing QTL syntax should be correct") {
    val policyText = "EXISTS x. P(x)"

    val expectedQTL = "Exists x. P(x)"

    val formula = Policy.parse(policyText).right.value
    val qtlString = formula.toQTL

    println(qtlString)
    println(expectedQTL)

    qtlString shouldBe expectedQTL
  }

  // ---------------------------------------------------------------------------
  // QTL translation. The expected strings below are cross-checked by the
  // integration suite in test/integration, which runs VeriMon on the original
  // policy and DejaVu on the translated one and compares their verdicts.
  // ---------------------------------------------------------------------------

  val E = Pred[String]("e")

  private def qtl(policy: String, neg: Boolean = true): String =
    Policy.parse(policy).right.value.toQTLString(neg, E)

  private def translationError(policy: String): String =
    intercept[UnsupportedOperationException] { qtl(policy) }.getMessage

  test("QTL translation: predicates become boundary lets of the reference shape") {
    val (fma, lets) = Policy.parse("PREVIOUS P0(x)").right.value.translateToQTL(E)
    val lifted = And(E, Prev(Interval.any, Since(Interval.any, Not(E), Pred[String]("P0", Var("x")))))
    lets shouldBe Map(Pred[String]("_P0", Var("x")) -> lifted)
    fma shouldBe And(E, Prev(Interval.any, Since(Interval.any, Not(E), Pred[String]("_P0", Var("x")))))
  }

  test("QTL translation: PREVIOUS refers to the previous database, not the current one") {
    qtl("PREVIOUS P0(x)") shouldBe
      "prop fma: ! Exists x. (e() & @  (! e() S  _P0(x))) where _P0(x) := e() & @  (! e() S  P0(x))"
  }

  test("QTL translation: PREVIOUS TRUE distinguishes the first database") {
    qtl("PREVIOUS TRUE") shouldBe "prop fma: ! (e() & @  (! e() S  e()))"
  }

  test("QTL translation: metric PREVIOUS puts the interval on the inner SINCE") {
    qtl("PREVIOUS [0,2] P0(x)") shouldBe
      "prop fma: ! Exists x. (e() & @  (! e() S [<= 2 ] _P0(x))) where _P0(x) := e() & @  (! e() S  P0(x))"
  }

  test("QTL translation: SINCE skips raw positions via the epred disjunct") {
    qtl("(A(x) AND B(x)) SINCE C(x)") shouldBe
      "prop fma: ! Exists x. ((((_A(x) & _B(x)) | ! e()) S  _C(x)) & e()) where " +
        "_A(x) := e() & @  (! e() S  A(x)), _B(x) := e() & @  (! e() S  B(x)), _C(x) := e() & @  (! e() S  C(x))"
  }

  test("QTL translation: negation is guarded so it cannot hold at raw positions") {
    qtl("ONCE (NOT P0())") shouldBe
      "prop fma: ! (((e() | ! e()) S  (! _P0() & e())) & e()) where _P0() := e() & @  (! e() S  P0())"
    qtl("P1(x) AND (NOT P0(x))") shouldBe
      "prop fma: ! Exists x. (_P1(x) & (! _P0(x) & e())) where " +
        "_P1(x) := e() & @  (! e() S  P1(x)), _P0(x) := e() & @  (! e() S  P0(x))"
  }

  test("QTL translation: equality is guarded so it cannot hold at raw positions") {
    qtl("(x = 3) AND ONCE P0(x)") shouldBe
      "prop fma: ! Exists x. ((x = 3 & e()) & (((e() | ! e()) S  _P0(x)) & e())) where " +
        "_P0(x) := e() & @  (! e() S  P0(x))"
  }

  test("QTL translation: equalities with a constant on the left are flipped") {
    qtl("(3 = x) AND ONCE P0(x)") shouldBe qtl("(x = 3) AND ONCE P0(x)")
    qtl("""("foo" = x) AND ONCE P0(x)""") shouldBe qtl("""(x = "foo") AND ONCE P0(x)""")
  }

  test("QTL translation: constant-constant equalities are evaluated statically") {
    qtl("(3 = 3) AND P0(x)") shouldBe
      "prop fma: ! Exists x. (e() & _P0(x)) where _P0(x) := e() & @  (! e() S  P0(x))"
    qtl("(3 = 4) AND P0(x)") shouldBe
      "prop fma: ! Exists x. (false & _P0(x)) where _P0(x) := e() & @  (! e() S  P0(x))"
  }

  test("QTL translation: inequalities are guarded and printed for DejaVu") {
    qtl("(x < 30) AND ONCE P0(x)") shouldBe
      "prop fma: ! Exists x. ((x < 30 & e()) & (((e() | ! e()) S  _P0(x)) & e())) where " +
        "_P0(x) := e() & @  (! e() S  P0(x))"
    qtl("Q(x,y) AND (x < y)") shouldBe
      "prop fma: ! Exists y. Exists x. (_Q(x, y) & (x < y & e())) where _Q(x, y) := e() & @  (! e() S  Q(x, y))"
  }

  test("QTL translation: inequalities with a constant on the left are mirrored") {
    qtl("(3 < x) AND ONCE P0(x)") shouldBe qtl("(x > 3) AND ONCE P0(x)")
    qtl("(3 <= x) AND ONCE P0(x)") shouldBe qtl("(x >= 3) AND ONCE P0(x)")
    qtl("(30 > x) AND ONCE P0(x)") shouldBe qtl("(x < 30) AND ONCE P0(x)")
    qtl("(30 >= x) AND ONCE P0(x)") shouldBe qtl("(x <= 30) AND ONCE P0(x)")
  }

  test("QTL translation: constant-constant inequalities are evaluated statically") {
    qtl("(3 < 4.5) AND P0(x)") shouldBe
      "prop fma: ! Exists x. (e() & _P0(x)) where _P0(x) := e() & @  (! e() S  P0(x))"
    qtl("(4 <= 3) AND P0(x)") shouldBe
      "prop fma: ! Exists x. (false & _P0(x)) where _P0(x) := e() & @  (! e() S  P0(x))"
    intercept[UnsupportedOperationException] {
      Rel(LT(), Const[String]("a"), Const[String]("b")).toQTLString(true, E)
    }.getMessage should include ("non-numeric")
  }

  test("QTL translation: metric SINCE intervals") {
    qtl("P1(x) SINCE [0,3) P0(x)") shouldBe
      "prop fma: ! Exists x. (((_P1(x) | ! e()) S [<= 2 ] _P0(x)) & e()) where " +
        "_P1(x) := e() & @  (! e() S  P1(x)), _P0(x) := e() & @  (! e() S  P0(x))"
    qtl("P1(x) SINCE [2,*) P0(x)") shouldBe
      "prop fma: ! Exists x. (((_P1(x) | ! e()) S [> 1 ] _P0(x)) & e()) where " +
        "_P1(x) := e() & @  (! e() S  P1(x)), _P0(x) := e() & @  (! e() S  P0(x))"
  }

  test("QTL translation: LET bodies are expanded at their use sites") {
    qtl("LET A(x) = P0(x) AND P1(x) IN A(x) SINCE P2(x)") shouldBe
      "prop fma: ! Exists x. ((((_P0(x) & _P1(x)) | ! e()) S  _P2(x)) & e()) where " +
        "_P0(x) := e() & @  (! e() S  P0(x)), _P1(x) := e() & @  (! e() S  P1(x)), _P2(x) := e() & @  (! e() S  P2(x))"
  }

  test("LET expansion substitutes arguments and avoids variable capture") {
    val phi = Policy.parse("LET A(x) = EXISTS y. Q(x,y) IN A(y)").right.value
    GenFormula.expandLets(phi) shouldBe Policy.parse("EXISTS y_1. Q(y,y_1)").right.value
  }

  test("LET expansion resolves nested definitions of the same name by scope") {
    val phi = Policy.parse("LET A() = P0(1) IN LET A() = A() AND P1(2) IN A()").right.value
    GenFormula.expandLets(phi) shouldBe Policy.parse("P0(1) AND P1(2)").right.value
  }

  test("QTL translation: one let per predicate and argument combination") {
    qtl("P0(x) AND PREVIOUS P0(y)") shouldBe
      "prop fma: ! Exists y. Exists x. (_P0(x) & (e() & @  (! e() S  _P0(y)))) where " +
        "_P0(x) := e() & @  (! e() S  P0(x)), _P0(y) := e() & @  (! e() S  P0(y))"
  }

  test("QTL translation: constant arguments are inlined instead of generating a macro") {
    qtl("ONCE P0(3)") shouldBe
      "prop fma: ! (((e() | ! e()) S  (e() & @  (! e() S  P0(3)))) & e())"
    qtl("""ONCE P0("foo")""") shouldBe
      """prop fma: ! (((e() | ! e()) S  (e() & @  (! e() S  P0("foo")))) & e())"""
  }

  test("QTL translation: repeated variable arguments are inlined instead of generating a macro") {
    qtl("P0(x,x) AND PREVIOUS P1(z)") shouldBe
      "prop fma: ! Exists z. Exists x. ((e() & @  (! e() S  P0(x, x))) & (e() & @  (! e() S  _P1(z)))) where " +
        "_P1(z) := e() & @  (! e() S  P1(z))"
  }

  test("Bound variables are renamed apart so DejaVu accepts shadowed quantifiers") {
    val phi = Policy.parse("(EXISTS y. P0(y)) AND P1(y)").right.value
    GenFormula.uniquifyBoundVariables(phi) shouldBe
      Policy.parse("(EXISTS y_1. P0(y_1)) AND P1(y)").right.value
    qtl("(EXISTS y. P0(y)) AND P1(y)") shouldBe
      "prop fma: ! Exists y. (Exists y_1. _P0(y_1) & _P1(y)) where " +
        "_P0(y_1) := e() & @  (! e() S  P0(y_1)), _P1(y) := e() & @  (! e() S  P1(y))"
  }

  test("QTL translation: a formula without predicates produces no where clause") {
    qtl("TRUE") shouldBe "prop fma: ! e()"
  }

  test("QTL translation: the positive mode restricts verdicts to boundary events") {
    qtl("PREVIOUS P0(x)", neg = false) shouldBe
      "prop fma: ! e() | Forall x. (e() & @  (! e() S  _P0(x))) where _P0(x) := e() & @  (! e() S  P0(x))"
    qtl("TRUE", neg = false) shouldBe "prop fma: ! e() | e()"
  }

  test("QTL translation: the event predicate must not occur in the formula") {
    translationError("P0(x) AND e()") should include ("event predicate")
  }

  test("QTL translation: predicates used with several arities are rejected") {
    translationError("P0(x) AND PREVIOUS P0(x,y)") should include ("different arities")
  }

  test("QTL translation: unsupported operators are rejected with a clear error") {
    translationError("HISTORICALLY P0(x)") should include ("not supported")
    translationError("NEXT P0(x)") should include ("not supported")
    translationError("EVENTUALLY P0(x)") should include ("not supported")
    translationError("P0(x) UNTIL P1(x)") should include ("not supported")
    translationError("c <- CNT x P0(x)") should include ("not supported")
  }

  test("QTL translation: double-bounded intervals are rejected") {
    translationError("P0(x) SINCE [1,3) P1(x)") should include ("Double-bounded")
  }

}
