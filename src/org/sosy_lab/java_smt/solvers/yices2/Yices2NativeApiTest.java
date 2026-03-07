// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;

import com.sri.yices.Config;
import com.sri.yices.Constructor;
import com.sri.yices.Context;
import com.sri.yices.InterpolationContext;
import com.sri.yices.Parameters;
import com.sri.yices.Status;
import com.sri.yices.Terms;
import com.sri.yices.Types;
import com.sri.yices.Yices;
import com.sri.yices.YicesException;
import java.math.BigInteger;
import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.rationals.Rational;

public class Yices2NativeApiTest {

  @BeforeClass
  public static void loadYices() {
    NativeLibraries.loadLibrary("yices2java");
    Yices.isReady();
  }

  private Context env;

  private Context newContext(boolean mcsat) {
    try (var cfg = new Config()) {
      cfg.set("solver-type", mcsat ? "mcsat" : "dpllt");
      cfg.set("mode", "interactive");
      cfg.set("model-interpolation", "true");
      return new Context(cfg);
    }
  }

  @Before
  public void createEnvironment() {
    env = newContext(false);
  }

  @After
  public void freeEnvironment() {
    env.close();
  }

  @Test
  public void simpleUNSAT() {
    int termTrue = Terms.mkTrue();
    int termFalse = Terms.mkFalse();
    int formula = Terms.and(termTrue, termFalse);
    env.assertFormula(formula);
    assertThat(env.check()).isEqualTo(Status.UNSAT);
  }

  @Test
  public void simpleSAT() {
    int termTrue = Terms.mkTrue();
    int formula = Terms.and(termTrue, termTrue);
    env.assertFormula(formula);
    assertThat(env.check()).isEqualTo(Status.SAT);
  }

  // 3=SAT 4=UNSAT
  @Test
  public void arrayArgSAT() {
    int termTrue = Terms.mkTrue();
    int[] terms = {termTrue, termTrue, termTrue, termTrue};
    int formula = Terms.and(terms);
    env.assertFormula(formula);
    assertThat(env.check()).isEqualTo(Status.SAT);
  }

  @Test
  public void arrayArgUNSAT() {
    int termTrue = Terms.mkTrue();
    int termFalse = Terms.mkFalse();
    int[] terms = {termFalse, termTrue, termTrue, termTrue};
    int formula = Terms.and(terms);
    env.assertFormula(formula);
    assertThat(env.check()).isEqualTo(Status.UNSAT);
  }

  @Test
  public void arithAddSAT() {
    int one = Terms.intConst(1);
    int two = Terms.intConst(2);
    int three = Terms.intConst(3);
    int add = Terms.add(one, two);
    int equal = Terms.eq(three, add);
    env.assertFormula(equal);
    assertThat(env.check()).isEqualTo(Status.SAT);
  }

  @Test
  public void arithAddUNSAT() {
    int one = Terms.intConst(1);
    int two = Terms.intConst(99);
    int three = Terms.intConst(3);
    int add = Terms.add(one, two);
    int equal = Terms.eq(three, add);
    env.assertFormula(equal);
    assertThat(env.check()).isEqualTo(Status.UNSAT);
  }

  @SuppressWarnings("CheckReturnValue")
  @Test
  public void rationalError() {
    assertThrows(YicesException.class, () -> Terms.rationalConst(1, 0));
  }

  @Test
  public void negativeRationalError() {
    // TODO negative unsigned integer causes no error. Need to ensure positive value before
    assertThat(Terms.rationalConst(1, -5)).isGreaterThan(0);
  }

  @SuppressWarnings("CheckReturnValue")
  @Test
  public void wrongType() {
    int one = Terms.intConst(1);
    assertThrows(YicesException.class, () -> Terms.bitSize(one));
  }

  @Test
  public void testRange() {
    /*
    int intmax = yices_int32(Integer.MAX_VALUE);
    int longmax = yices_int64(Long.MAX_VALUE);
    int gt = yices_arith_gt_atom(longmax, intmax);
    env.assertFormula(gt);
    assertThat(env.check()).isEqualTo(SAT);

    */
    throw new AssertionError("yices_int32 not supported");
  }

  @Test
  public void simpleBitvectorSAT() {
    int v1 = Terms.parseBvBin("01010");
    int v2 = Terms.parseBvBin("10101");
    int v3 = Terms.bvOne(1);
    int f1 = Terms.bvXor(v1, v2);
    int f2 = Terms.bvRedAnd(f1);
    int f3 = Terms.bvEq(f2, v3);
    env.assertFormula(f3);
    assertThat(env.check()).isEqualTo(Status.SAT);
  }

  @Test
  public void simpleBitvectorUNSAT() {
    int v1 = Terms.parseBvBin("01010");
    int v2 = Terms.parseBvBin("10101");
    int v3 = Terms.bvOne(1);
    int f1 = Terms.bvAnd(v1, v2);
    int f2 = Terms.bvRedAnd(f1);
    int f3 = Terms.bvEq(f2, v3);
    env.assertFormula(f3);
    assertThat(env.check()).isEqualTo(Status.UNSAT);
  }

  @Test
  public void boolValueQuery() {
    int v1 = Terms.mkTrue();
    int v2 = Terms.mkFalse();
    assertThat(Terms.boolConstValue(v1)).isTrue();
    assertThat(Terms.boolConstValue(v2)).isFalse();
  }

  @Test
  public void boolValueTypeMismatch() {
    int v1 = Terms.intConst(45);
    assertThrows(YicesException.class, () -> Terms.boolConstValue(v1));
  }

  @Test
  public void bitvectorReturn() {
    int bv1 = Terms.parseBvBin("111000");
    boolean[] bvComp = {false, false, false, true, true, true};
    int bvsize = Terms.bitSize(bv1);
    assertThat(bvsize).isEqualTo(6);
    boolean[] bvReturn = Terms.bvConstValue(bv1);
    assertThat(bvComp).isEqualTo(bvReturn);
  }

  @Test
  public void rationalValueTest() {
    int num = 35975;
    int den = 1234567890;
    int negativeNum = -50;
    int negativeDen = -30000;
    BigInteger largeNumber = BigInteger.valueOf(2).pow(10000);
    int ratConst = Terms.rationalConst(num, den);
    int negativeNumConst = Terms.parseRational(negativeNum + "/" + den);
    int negativeDenConst = Terms.parseRational(num + "/" + negativeDen);
    int negativeNumDenConst = Terms.parseRational(negativeNum + "/" + negativeDen);
    int bigConst = Terms.parseRational(largeNumber.toString());
    Yices2FormulaCreator creator = new Yices2FormulaCreator();
    assertThat(creator.convertValue(ratConst, ratConst)).isEqualTo(Rational.of(num + "/" + den));
    assertThat(creator.convertValue(bigConst, bigConst)).isEqualTo(largeNumber);
    assertThat(creator.convertValue(negativeNumConst, negativeNumConst))
        .isEqualTo(Rational.of(negativeNum + "/" + den));
    assertThat(creator.convertValue(negativeDenConst, negativeDenConst))
        .isEqualTo(Rational.of(num + "/" + negativeDen));
    assertThat(creator.convertValue(negativeNumDenConst, negativeNumDenConst))
        .isEqualTo(Rational.of(negativeNum + "/" + negativeDen));
  }

  @Test
  public void bvValueTest() {
    long value = 14;
    int bv = Terms.bvConst(4, value);
    if (Terms.constructor(bv) == Constructor.BV_CONSTANT) {
      boolean[] bits = Terms.bvConstValue(bv);
      var big = BigInteger.ZERO;
      for (var p = 0; p < bits.length; p++) {
        if (bits[p]) {
          big = big.setBit(p);
        }
      }
      assertThat(big).isEqualTo(BigInteger.valueOf(value));
    }
  }

  @Test
  public void termNaming() {
    int t = Terms.parseBvBin("0100100001100101011011000110110001101111");
    String termName = "Hello";
    Terms.setName(t, termName);
    assertThat(Terms.getName(t)).isEqualTo(termName);
  }

  @Test
  public void satWithVariable() {
    int termFalse = Terms.mkFalse();
    int var = Terms.newUninterpretedTerm(Types.boolType());
    int formula = Terms.or(termFalse, var);
    env.assertFormula(formula);
    assertThat(env.check()).isEqualTo(Status.SAT);
  }

  // Yices converts add(YICES_ARITH_CONST, YICES_ARITH_CONST) to an YICES_ARITH_CONST
  // Yices converts add(YICES_ARITH_CONST, YICES_UNINTERPRETED_TERM) to YICES_ARITH_SUM
  @Test
  public void termConstructorAdd() {
    int one = Terms.intConst(1);
    int two = Terms.newUninterpretedTerm(Types.intType()); // Terms.intConst(2);
    int addition = Terms.add(one, two);
    assertThat(Terms.constructor(addition)).isEqualTo(Constructor.ARITH_SUM);
  }

  @Test
  public void termConstructorAnd() {
    // and 1 2 is replaced with not (or (not 1) (not 2))
    int termTrue = Terms.newUninterpretedTerm(Types.boolType()); // Terms.mkTrue();
    Terms.setName(termTrue, "termTrue");
    int termTwo = Terms.newUninterpretedTerm(Types.boolType());
    Terms.setName(termTwo, "termTwo");
    int and = Terms.and(termTrue, termTwo);

    int child = Terms.child(and, 0);
    assertThat(Terms.constructor(child)).isEqualTo(Constructor.OR_TERM);
    assertThat(Terms.numChildren(child)).isEqualTo(2);
    assertThat(Terms.toString(and)).isEqualTo("(and termTrue termTwo)");
    assertThat(Terms.constructor(and)).isEqualTo(Constructor.NOT_TERM);
  }

  @Test
  public void termConstructorOr() {
    int termFalse = Terms.newUninterpretedTerm(Types.boolType()); // Terms.mkFalse();
    // Terms.setName(termFalse, "1");
    int two = Terms.newUninterpretedTerm(Types.boolType());
    // Terms.setName(two, "5");
    int[] orArray = {termFalse, two, termFalse, termFalse};
    int or = Terms.or(orArray);
    assertThat(Terms.isBool(or)).isTrue();
    assertThat(Terms.constructor(or)).isEqualTo(Constructor.OR_TERM);
    // Works after changing something?
  } // Expecting YICES_OR_TERM as constructor but getting YICES_UNINTERPRETED_TERM

  @Test
  public void termConstructorNot() {
    int termTrue = Terms.newUninterpretedTerm(Types.boolType()); // Terms.mkTrue();
    Terms.setName(termTrue, "termTrue");
    int termTwo = Terms.newUninterpretedTerm(Types.boolType());
    Terms.setName(termTwo, "termTwo");
    int not = Terms.not(termTrue);
    assertThat(Terms.constructor(not)).isEqualTo(Constructor.NOT_TERM);
  }

  @Test
  public void modularCongruence() {
    int pNumber1 = Terms.intConst(9);
    int pNumber2 = Terms.intConst(5);
    int mod = Terms.intConst(4);
    int subTerm = Terms.sub(pNumber1, pNumber2);
    int div = Terms.idiv(subTerm, mod);
    int mul = Terms.mul(mod, div);
    int eq = Terms.arithEq(subTerm, mul);
    assertThat(eq).isEqualTo(Terms.mkTrue());
  }

  @Test
  public void orSimplification() {
    int termTrue = Terms.mkTrue();
    int boolType = Types.boolType();
    int[] orArray = new int[20];
    for (int i = 0; i < (orArray.length - 1); i++) {
      orArray[i] = Terms.newUninterpretedTerm("x" + i, boolType);
    }
    orArray[(orArray.length - 1)] = termTrue;
    int or = Terms.or(orArray);
    assertThat(or).isEqualTo(Terms.mkTrue());
  }

  @Test
  public void andSimplification() {
    int termFalse = Terms.mkFalse();
    int boolType = Types.boolType();
    int[] andArray = new int[20];
    for (int i = 0; i < (andArray.length - 1); i++) {
      andArray[i] = Terms.newUninterpretedTerm("x" + i, boolType);
    }
    andArray[(andArray.length - 1)] = termFalse;
    int and = Terms.and(andArray);
    assertThat(and).isEqualTo(Terms.mkFalse());
  }

  @Test
  public void iffConstructor() {
    int one = Terms.newUninterpretedTerm(Types.boolType());
    int two = Terms.newUninterpretedTerm(Types.boolType());
    int iff = Terms.iff(one, two);
    assertThat(Terms.constructor(iff)).isEqualTo(Constructor.EQ_TERM);
  }

  @Test
  public void ufConstructor() {
    int funType = Types.functionType(new int[] {Types.intType()}, Types.boolType());
    int uf = Terms.newUninterpretedTerm("uf", funType);
    int[] argArray = new int[] {Terms.intConst(123)};
    int app = Terms.funApplication(uf, argArray);
    assertThat(Terms.constructor(app)).isEqualTo(Constructor.APP_TERM);
  }

  @Test
  public void uf2Constructor() {
    int funType = Types.functionType(Types.intType(), Types.intType(), Types.intType());
    int uf = Terms.newUninterpretedTerm("uf", funType);
    int[] argArray = new int[] {Terms.intConst(123), Terms.intConst(456)};
    int app = Terms.funApplication(uf, argArray);
    assertThat(Terms.constructor(app)).isEqualTo(Constructor.APP_TERM);
  }

  @Test
  public void parseTerm() {
    // int x = yices_parse_term("define x::int");
    // int y = yices_parse_term("define y::int");
    // int xsmallery = yices_parse_term("assert (< x y)");
    // int xbigger4 = yices_parse_term("assert (> x 4)");
    // int ysmaller7 = yices_parse_term("assert (< y 7)");
    // assertThat(env.check(), SAT);
    int y = Terms.intConst(5);
    Terms.setName(y, "y");
    int x = Terms.parse("(/= y 5)");
    assertThat(Terms.toString(x)).isEqualTo("false");
  }

  @Test
  public void arithSimplification() {
    int x = Terms.intConst(6);
    int y = Terms.intConst(7);
    int add = Terms.add(x, y);
    int mul = Terms.mul(x, y);
    Yices2FormulaCreator creator = new Yices2FormulaCreator();
    assertThat(creator.convertValue(add, add)).isEqualTo(BigInteger.valueOf(13));
    assertThat(Terms.constructor(add)).isEqualTo(Constructor.ARITH_CONSTANT);
    assertThat(creator.convertValue(mul, mul)).isEqualTo(BigInteger.valueOf(42));
    assertThat(Terms.constructor(mul)).isEqualTo(Constructor.ARITH_CONSTANT);
  }

  @Test
  public void sumComponents() {
    /*
    int three = Terms.intConst(3);
    int rat = Terms.parseRational("3/2");
    int x = Terms.newUninterpretedTerm(Types.intType(), "x");
    int[] oneX = {three, x};
    int sumOneX = yices_sum(2, oneX);
    for (int i = 0; i < Terms.numChildren(sumOneX); i++) {
      assertThat(Terms.toString(sumOneX)).isNotNull();
      assertThat(Arrays.toString(yices_sum_component(sumOneX, i))).isNotNull();
    }
    int[] twoX = {three, x, x};
    int sumTwoX = yices_sum(3, twoX);
    for (int i = 0; i < Terms.numChildren(sumTwoX); i++) {
      assertThat(Terms.toString(sumTwoX)).isNotNull();
      assertThat(Arrays.toString(yices_sum_component(sumTwoX, i))).isNotNull();
    }
    int[] twoThrees = {three, x, three};
    int sumTwoThrees = yices_sum(3, twoThrees);
    for (int i = 0; i < Terms.numChildren(sumTwoThrees); i++) {
      assertThat(Terms.toString(sumTwoThrees)).isNotNull();
      assertThat(Arrays.toString(yices_sum_component(sumTwoThrees, i))).isNotNull();
    }
    int xTimesRational = Terms.bvMul(rat, x);
    int[] ratSum = {three, xTimesRational};
    int sumRatX = yices_sum(2, ratSum);
    for (int i = 0; i < Terms.numChildren(sumRatX); i++) {
      assertThat(Terms.toString(sumRatX)).isNotNull();
      assertThat(Arrays.toString(yices_sum_component(sumRatX, i))).isNotNull();
    }
    */
    throw new AssertionError("sums not supported");
  }

  @Test
  public void bvSumComponents() {
    /*
    String bv1StringValue = "00101";
    int bv1 = Terms.parseBvBin(bv1StringValue);
    int bv5type = Types.bvType(5);
    int x = Terms.newUninterpretedTerm(bv5type, "x");
    int negativeX = Terms.bvMul(Terms.bvMinusOne(5), x);
    int add = Terms.bvAdd(bv1, negativeX);
    assertThat(Terms.numChildren(add)).isEqualTo(2);
    assertThat(Terms.toString(add)).isNotNull();

    int[] component1 = yices_bvsum_component(add, 0, Terms.bitSize(add));
    String value1 =
        Joiner.on("")
            .join(
                Lists.reverse(
                    Ints.asList(Arrays.copyOfRange(component1, 0, component1.length - 1))));
    int term1 = component1[component1.length - 1];
    // Value of coefficient
    assertThat(value1).isEqualTo(bv1StringValue);
    // Coefficient as BigInt
    assertThat(new BigInteger(value1, 2)).isEqualTo(BigInteger.valueOf(5));
    // Term id is NULL (-1) for i = 0
    assertThat(term1).isEqualTo(-1);

    int[] component2 = yices_bvsum_component(add, 1, Terms.bitSize(add));
    String value2 =
        Joiner.on("")
            .join(
                Lists.reverse(
                    Ints.asList(Arrays.copyOfRange(component2, 0, component2.length - 1))));
    int term2 = component2[component2.length - 1];
    // Value of coefficient (-1 == 11111)
    assertThat(value2).isEqualTo("11111");
    // Coefficient as BigInt (31 because it has no sign bit, and -1 is max for bv)
    assertThat(new BigInteger(value2, 2)).isEqualTo(BigInteger.valueOf(31));
    // Term id is NULL (-1) for i = 0
    assertThat(term2).isEqualTo(x);
    */
    throw new AssertionError("sums not supported");
  }

  @SuppressWarnings("CheckReturnValue")
  @Test
  public void bvExtensionStructureTest() {
    int initialSize = 5;
    int extendBy = 5;
    int x = Terms.newUninterpretedTerm("x", Types.bvType(initialSize));
    int signExtendedX = Terms.bvSignExtend(x, extendBy);
    int zeroExtendedX = Terms.bvZeroExtend(x, extendBy);

    assertThat(Terms.toString(x)).isNotNull();
    assertThat(Terms.numChildren(x)).isEqualTo(0);
    assertThat(Terms.numChildren(signExtendedX)).isEqualTo(initialSize + extendBy);
    assertThat(Terms.toString(signExtendedX)).isNotNull();
    assertThat(Terms.numChildren(zeroExtendedX)).isEqualTo(initialSize + extendBy);
    assertThat(Terms.toString(zeroExtendedX)).isNotNull();

    int bvSignExt = Terms.projArg(Terms.child(signExtendedX, 0));
    int bvSizeSignExt = Terms.bitSize(bvSignExt);
    int extendedBySignExt = Terms.numChildren(signExtendedX) - bvSizeSignExt;
    assertThat(extendedBySignExt).isEqualTo(extendBy);

    int bvZeroExt = Terms.projArg(Terms.child(zeroExtendedX, 0));
    int bvSizeZeroExt = Terms.bitSize(bvZeroExt);
    int extendedByZeroExt = Terms.numChildren(zeroExtendedX) - bvSizeZeroExt;
    assertThat(extendedByZeroExt).isEqualTo(extendBy);

    assertThat(Terms.child(zeroExtendedX, bvSizeZeroExt)).isEqualTo(Terms.mkFalse());
    assertThat(Terms.child(signExtendedX, bvSizeSignExt)).isNotEqualTo(Terms.mkFalse());

    assertThrows(YicesException.class, () -> Terms.projArg(Terms.child(x, 0)));
  }

  @Test
  public void booleanParse() {
    int test = Terms.parse("false");
    assertThat(Terms.mkFalse()).isEqualTo(test);
    int test2 = Terms.parse("true");
    assertThat(Terms.mkTrue()).isEqualTo(test2);
  }

  @Test
  public void bvSum() {
    int type = Types.bvType(5);
    int bv1 = Terms.newUninterpretedTerm("x", type);
    int bv2 = Terms.newUninterpretedTerm("y", type);
    int add = Terms.bvAdd(bv1, bv2);
    Constructor constructor = Terms.constructor(add);
    assertThat(constructor).isEqualTo(Constructor.BV_SUM);
  }

  @Test
  public void bvMul() {
    /*
    int type = Types.bvType(5);
    int bv2 = Terms.newUninterpretedTerm(type, "x");
    int mul = Terms.bvMul(bv2, bv2);
    assertThat(Terms.constructor(mul)).isEqualTo(Constructor.POWER_PRODUCT);
    // bv2 + bv2 == bv2²
    int[] component = yices_product_component(mul, 0);
    assertThat(component[0]).isEqualTo(bv2);
    assertThat(component[1]).isEqualTo(2);
    assertThat(Terms.constructor(yices_bvpower(component[0], component[1]))).isGreaterThan(0);
    */
    throw new AssertionError("products not supported");
  }

  @Test
  public void isThreadSafe() {
    // Check that we compiled with --enable-thread-safety to make it reentrant
    assertThat(Yices.isThreadSafe()).isTrue();
  }

  @Test
  public void hasMCSat() {
    // Check that we compiled with --enable-mcsat
    assertThat(Yices.hasMcsat()).isTrue();
  }

  @Test
  public void checkVersion() {
    assertThat(Yices.version()).isEqualTo("2.7.0");
  }

  @Test
  public void quantifierTest() {
    int boundVar = Terms.newVariable(Types.intType());
    int eleven = Terms.intConst(11);
    int body = Terms.eq(eleven, boundVar);

    int forall = Terms.forall(new int[] {boundVar}, body);
    int exists = Terms.exists(new int[] {boundVar}, body);

    assertThat(Terms.constructor(forall)).isEqualTo(Constructor.FORALL_TERM);
    assertThat(Terms.constructor(exists)).isEqualTo(Constructor.NOT_TERM);
    assertThat(Terms.constructor(Terms.child(exists, 0))).isEqualTo(Constructor.FORALL_TERM);
  }

  @Test
  public void booleanInterpolationTest() {
    var boolType = Types.boolType();
    var a = Terms.newUninterpretedTerm("a", boolType);

    try (var ctxA = newContext(true);
        var ctxB = newContext(true)) {

      ctxA.assertFormula(a);
      ctxB.assertFormula(Terms.not(a));

      var context = new InterpolationContext(ctxA, ctxB);

      try (var param = new Parameters()) {
        var status = context.check(param, false);

        assertThat(status).isEqualTo(Status.UNSAT);
        assertThat(context.getInterpolant()).isEqualTo(a);
      }
    }
  }
}
