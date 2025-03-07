// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static com.google.common.truth.Truth.assertThat;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_APP_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_SUM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SUM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_EQ_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_NOT_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_OR_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_POWER_PRODUCT;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_add;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_and;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_and2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_application;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_eq_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_gt_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_assert_formula;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bool_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bool_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bv_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bv_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvadd;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvand2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvconst_int64;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvconst_minus_one;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvconst_one;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bveq_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvmul;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvpower;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsum_component;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvxor2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_check_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_context_disable_option;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_eq;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_exit;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_false;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_function_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_term_by_name;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_term_name;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_idiv;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_iff;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_init;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int32;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int64;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_mul;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_uninterpreted_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_not;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_or;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_or2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_bvbin;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_rational;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_product_component;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_proj_arg;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_rational32;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_redand;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_set_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_set_term_name;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_sign_extend;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_sub;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_sum;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_sum_component;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_bitsize;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_child;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_constructor;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_is_bool;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_num_children;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_true;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_of_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_zero_extend;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.primitives.Ints;
import java.math.BigInteger;
import java.util.Arrays;
import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.rationals.Rational;

@SuppressWarnings("unused")
public class Yices2NativeApiTest {
  private static final int SAT = 3;
  private static final int UNSAT = 4;

  @BeforeClass
  public static void loadYices() {
    try {
      NativeLibraries.loadLibrary("yices2j");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("Yices2 is not available", e);
    }
  }

  private long env;

  @Before
  public void createEnvironment() {
    yices_init();
    long cfg = yices_new_config();
    yices_set_config(cfg, "solver-type", "dpllt");
    yices_set_config(cfg, "mode", "push-pop");
    env = yices_new_context(cfg);
    yices_context_disable_option(env, "var-elim");
    yices_free_config(cfg);
  }

  @After
  public void freeEnvironment() {
    yices_free_context(env);
    yices_exit();
  }

  @Test
  public void simpleUNSAT() {
    int termTrue = yices_true();
    int termFalse = yices_false();
    int formula = yices_and2(termTrue, termFalse);
    yices_assert_formula(env, formula);
    assertThat(yices_check_context(env, 0)).isEqualTo(UNSAT);
  }

  @Test
  public void simpleSAT() {
    int termTrue = yices_true();
    int formula = yices_and2(termTrue, termTrue);
    yices_assert_formula(env, formula);
    assertThat(yices_check_context(env, 0)).isEqualTo(SAT);
  }

  /*
   * 3=SAT 4=UNSAT
   */
  @Test
  public void arrayArgSAT() {
    int n = 4;
    int termTrue = yices_true();
    int[] terms = {termTrue, termTrue, termTrue, termTrue};
    int formula = yices_and(n, terms);
    yices_assert_formula(env, formula);
    assertThat(yices_check_context(env, 0)).isEqualTo(SAT);
  }

  @Test
  public void arrayArgUNSAT() {
    int n = 4;
    int termTrue = yices_true();
    int termFalse = yices_false();
    int[] terms = {termFalse, termTrue, termTrue, termTrue};
    int formula = yices_and(n, terms);
    yices_assert_formula(env, formula);
    assertThat(yices_check_context(env, 0)).isEqualTo(UNSAT);
  }

  @Test
  public void arithAddSAT() {
    int one = yices_int32(1);
    int two = yices_int32(2);
    int three = yices_int32(3);
    int add = yices_add(one, two);
    int equal = yices_eq(three, add);
    yices_assert_formula(env, equal);
    assertThat(yices_check_context(env, 0)).isEqualTo(SAT);
  }

  @Test
  public void arithAddUNSAT() {
    int one = yices_int32(1);
    int two = yices_int32(99);
    int three = yices_int32(3);
    int add = yices_add(one, two);
    int equal = yices_eq(three, add);
    yices_assert_formula(env, equal);
    assertThat(yices_check_context(env, 0)).isEqualTo(UNSAT);
  }

  @SuppressWarnings("CheckReturnValue")
  @Test(expected = IllegalArgumentException.class)
  public void rationalError() {
    yices_rational32(1, 0);
  }

  @Test
  public void negativeRationalError() {
    // TODO negative unsigned integer causes no error. Need to ensure positive value before
    assertThat(yices_rational32(1, -5)).isGreaterThan(0);
  }

  @SuppressWarnings("CheckReturnValue")
  @Test(expected = IllegalArgumentException.class)
  public void wrongType() {
    int one = yices_int32(1);
    yices_term_bitsize(one);
  }

  @Test
  public void testRange() {
    int intmax = yices_int32(Integer.MAX_VALUE);
    int longmax = yices_int64(Long.MAX_VALUE);
    int gt = yices_arith_gt_atom(longmax, intmax);
    yices_assert_formula(env, gt);
    assertThat(yices_check_context(env, 0)).isEqualTo(SAT);
  }

  @Test
  public void simpleBitvectorSAT() {
    int v1 = yices_parse_bvbin("01010");
    int v2 = yices_parse_bvbin("10101");
    int v3 = yices_bvconst_one(1);
    int f1 = yices_bvxor2(v1, v2);
    int f2 = yices_redand(f1);
    int f3 = yices_bveq_atom(f2, v3);
    yices_assert_formula(env, f3);
    assertThat(yices_check_context(env, 0)).isEqualTo(SAT);
  }

  @Test
  public void simpleBitvectorUNSAT() {
    int v1 = yices_parse_bvbin("01010");
    int v2 = yices_parse_bvbin("10101");
    int v3 = yices_bvconst_one(1);
    int f1 = yices_bvand2(v1, v2);
    int f2 = yices_redand(f1);
    int f3 = yices_bveq_atom(f2, v3);
    yices_assert_formula(env, f3);
    assertThat(yices_check_context(env, 0)).isEqualTo(UNSAT);
  }

  @Test
  public void boolValueQuery() {
    int v1 = yices_true();
    int v2 = yices_false();
    assertThat(yices_bool_const_value(v1)).isTrue();
    assertThat(yices_bool_const_value(v2)).isFalse();
  }

  @SuppressWarnings("CheckReturnValue")
  @Test(expected = IllegalArgumentException.class)
  public void boolValueTypeMismatch() {
    int v1 = yices_int32(45);
    yices_bool_const_value(v1);
  }

  @Test
  public void bitvectorReturn() {
    int bv1 = yices_parse_bvbin("111000");
    int[] bvComp = {0, 0, 0, 1, 1, 1};
    int bvsize = yices_term_bitsize(bv1);
    assertThat(bvsize).isEqualTo(6);
    int[] bvReturn = yices_bv_const_value(bv1, bvsize);
    assertThat(bvComp).isEqualTo(bvReturn);
  }

  @Test
  public void rationalValueTest() {
    int num = 35975;
    int den = 1234567890;
    int negativeNum = -50;
    int negativeDen = -30000;
    BigInteger largeNumber = BigInteger.valueOf(2).pow(10000);
    int ratConst = yices_rational32(num, den);
    int negativeNumConst = yices_parse_rational(negativeNum + "/" + den);
    int negativeDenConst = yices_parse_rational(num + "/" + negativeDen);
    int negativeNumDenConst = yices_parse_rational(negativeNum + "/" + negativeDen);
    int bigConst = yices_parse_rational(largeNumber.toString());
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
    int value = 14;
    int bv = yices_bvconst_int64(4, value);
    if (yices_term_constructor(bv) == YICES_BV_CONST) {
      int[] littleEndianBV = yices_bv_const_value(bv, yices_term_bitsize(bv));
      Preconditions.checkArgument(littleEndianBV.length != 0, "BV was empty");
      String bigEndianBV = Joiner.on("").join(Lists.reverse(Ints.asList(littleEndianBV)));
      BigInteger big = new BigInteger(bigEndianBV, 2);
      assertThat(big).isEqualTo(BigInteger.valueOf(value));
    }
  }

  @Test
  public void termNaming() {
    int t = yices_parse_bvbin("0100100001100101011011000110110001101111");
    String termName = "Hello";
    yices_set_term_name(t, termName);
    assertThat(yices_get_term_name(t)).isEqualTo(termName);
  }

  @Test
  public void satWithVariable() {
    int termFalse = yices_false();
    int var = yices_new_uninterpreted_term(yices_bool_type());
    int formula = yices_or2(termFalse, var);
    yices_assert_formula(env, formula);
    assertThat(yices_check_context(env, 0)).isEqualTo(SAT);
  }

  // Yices converts add(YICES_ARITH_CONST, YICES_ARITH_CONST) to an YICES_ARITH_CONST
  // Yices converts add(YICES_ARITH_CONST, YICES_UNINTERPRETED_TERM) to YICES_ARITH_SUM
  @Test
  public void termConstructorAdd() {
    int one = yices_int32(1);
    int two = yices_new_uninterpreted_term(yices_int_type()); // yices_int32(2);
    int addition = yices_add(one, two);
    assertThat(yices_term_constructor(addition)).isEqualTo(YICES_ARITH_SUM);
  }

  @Test
  public void termConstructorAnd() {
    // and 1 2 is replaced with not (or (not 1) (not 2))
    int termTrue = yices_new_uninterpreted_term(yices_bool_type()); // yices_true();
    yices_set_term_name(termTrue, "termTrue");
    int termTwo = yices_new_uninterpreted_term(yices_bool_type());
    yices_set_term_name(termTwo, "termTwo");
    int and = yices_and2(termTrue, termTwo);

    int child = yices_term_child(and, 0);
    assertThat(yices_term_constructor(child)).isEqualTo(YICES_OR_TERM);
    assertThat(yices_term_num_children(child)).isEqualTo(2);
    assertThat(yices_term_to_string(and)).isEqualTo("(and termTrue termTwo)");
    assertThat(yices_term_constructor(and)).isEqualTo(YICES_NOT_TERM);
  }

  @Test
  public void termConstructorOr() {
    int termFalse = yices_new_uninterpreted_term(yices_bool_type()); // yices_false();
    // yices_set_term_name(termFalse, "1");
    int two = yices_new_uninterpreted_term(yices_bool_type());
    // yices_set_term_name(two, "5");
    int[] orArray = {termFalse, two, termFalse, termFalse};
    int or = yices_or(4, orArray);
    assertThat(yices_term_is_bool(or)).isTrue();
    assertThat(yices_term_constructor(or)).isEqualTo(YICES_OR_TERM);
    // Works after changing something?
  } // Expecting YICES_OR_TERM as constructor but getting YICES_UNINTERPRETED_TERM

  @Test
  public void termConstructorNot() {
    int termTrue = yices_new_uninterpreted_term(yices_bool_type()); // yices_true();
    yices_set_term_name(termTrue, "termTrue");
    int termTwo = yices_new_uninterpreted_term(yices_bool_type());
    yices_set_term_name(termTwo, "termTwo");
    int not = yices_not(termTrue);
    assertThat(yices_term_constructor(not)).isEqualTo(YICES_NOT_TERM);
  }

  @Test
  public void modularCongruence() {
    int pNumber1 = yices_int32(9);
    int pNumber2 = yices_int32(5);
    int mod = yices_int32(4);
    int subTerm = yices_sub(pNumber1, pNumber2);
    int div = yices_idiv(subTerm, mod);
    int mul = yices_mul(mod, div);
    int eq = yices_arith_eq_atom(subTerm, mul);
    assertThat(eq).isEqualTo(yices_true());
  }

  @Test
  public void orSimplification() {
    int termTrue = yices_true();
    int boolType = yices_bool_type();
    int[] orArray = new int[20];
    for (int i = 0; i < (orArray.length - 1); i++) {
      orArray[i] = yices_named_variable(boolType, "x" + i);
    }
    orArray[(orArray.length - 1)] = termTrue;
    int or = yices_or(orArray.length, orArray);
    assertThat(or).isEqualTo(yices_true());
  }

  @Test
  public void andSimplification() {
    int termFalse = yices_false();
    int boolType = yices_bool_type();
    int[] andArray = new int[20];
    for (int i = 0; i < (andArray.length - 1); i++) {
      andArray[i] = yices_named_variable(boolType, "x" + i);
    }
    andArray[(andArray.length - 1)] = termFalse;
    int and = yices_and(andArray.length, andArray);
    assertThat(and).isEqualTo(yices_false());
  }

  @Test
  public void iffConstructor() {
    int one = yices_new_uninterpreted_term(yices_bool_type());
    int two = yices_new_uninterpreted_term(yices_bool_type());
    int iff = yices_iff(one, two);
    assertThat(yices_term_constructor(iff)).isEqualTo(YICES_EQ_TERM);
  }

  @Test
  public void ufConstructor() {
    int funType = yices_function_type(1, new int[] {yices_int_type()}, yices_bool_type());
    int uf = yices_named_variable(funType, "uf");
    int[] argArray = new int[] {yices_int32(123)};
    int app = yices_application(uf, argArray.length, argArray);
    assertThat(yices_term_constructor(app)).isEqualTo(YICES_APP_TERM);
  }

  @Test
  public void uf2Constructor() {
    int funType =
        yices_function_type(2, new int[] {yices_int_type(), yices_int_type()}, yices_int_type());
    int uf = yices_named_variable(funType, "uf");
    int[] argArray = new int[] {yices_int32(123), yices_int32(456)};
    int app = yices_application(uf, argArray.length, argArray);
    assertThat(yices_term_constructor(app)).isEqualTo(YICES_APP_TERM);
  }

  @Test
  public void parseTerm() {
    // int x = yices_parse_term("define x::int");
    // int y = yices_parse_term("define y::int");
    // int xsmallery = yices_parse_term("assert (< x y)");
    // int xbigger4 = yices_parse_term("assert (> x 4)");
    // int ysmaller7 = yices_parse_term("assert (< y 7)");
    // assertThat(yices_check_context(env, 0), SAT);
    int y = yices_int32(5);
    yices_set_term_name(y, "y");
    int x = yices_parse_term("(/= y 5)");
    assertThat(yices_term_to_string(x)).isEqualTo("false");
  }

  @Test
  public void arithSimplification() {
    int x = yices_int32(6);
    int y = yices_int32(7);
    int add = yices_add(x, y);
    int mul = yices_mul(x, y);
    Yices2FormulaCreator creator = new Yices2FormulaCreator();
    assertThat(creator.convertValue(add, add)).isEqualTo(BigInteger.valueOf(13));
    assertThat(yices_term_constructor(add)).isEqualTo(YICES_ARITH_CONST);
    assertThat(creator.convertValue(mul, mul)).isEqualTo(BigInteger.valueOf(42));
    assertThat(yices_term_constructor(mul)).isEqualTo(YICES_ARITH_CONST);
  }

  @Test
  public void sumComponents() {
    int three = yices_int32(3);
    int rat = yices_parse_rational("3/2");
    int x = yices_named_variable(yices_int_type(), "x");
    int[] oneX = {three, x};
    int sumOneX = yices_sum(2, oneX);
    for (int i = 0; i < yices_term_num_children(sumOneX); i++) {
      assertThat(yices_term_to_string(sumOneX)).isNotNull();
      assertThat(Arrays.toString(yices_sum_component(sumOneX, i))).isNotNull();
    }
    int[] twoX = {three, x, x};
    int sumTwoX = yices_sum(3, twoX);
    for (int i = 0; i < yices_term_num_children(sumTwoX); i++) {
      assertThat(yices_term_to_string(sumTwoX)).isNotNull();
      assertThat(Arrays.toString(yices_sum_component(sumTwoX, i))).isNotNull();
    }
    int[] twoThrees = {three, x, three};
    int sumTwoThrees = yices_sum(3, twoThrees);
    for (int i = 0; i < yices_term_num_children(sumTwoThrees); i++) {
      assertThat(yices_term_to_string(sumTwoThrees)).isNotNull();
      assertThat(Arrays.toString(yices_sum_component(sumTwoThrees, i))).isNotNull();
    }
    int xTimesRational = yices_mul(rat, x);
    int[] ratSum = {three, xTimesRational};
    int sumRatX = yices_sum(2, ratSum);
    for (int i = 0; i < yices_term_num_children(sumRatX); i++) {
      assertThat(yices_term_to_string(sumRatX)).isNotNull();
      assertThat(Arrays.toString(yices_sum_component(sumRatX, i))).isNotNull();
    }
  }

  @Test
  public void bvSumComponents() {
    String bv1StringValue = "00101";
    int bv1 = yices_parse_bvbin(bv1StringValue);
    int bv5type = yices_bv_type(5);
    int x = yices_named_variable(bv5type, "x");
    int negativeX = yices_bvmul(yices_bvconst_minus_one(5), x);
    int add = yices_bvadd(bv1, negativeX);
    assertThat(yices_term_num_children(add)).isEqualTo(2);
    assertThat(yices_term_to_string(add)).isNotNull();

    int[] component1 = yices_bvsum_component(add, 0, yices_term_bitsize(add));
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

    int[] component2 = yices_bvsum_component(add, 1, yices_term_bitsize(add));
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
  }

  @Test(expected = IllegalArgumentException.class)
  public void bvExtensionStructureTest() {
    int initialSize = 5;
    int extendBy = 5;
    int x = yices_named_variable(yices_bv_type(initialSize), "x");
    int signExtendedX = yices_sign_extend(x, extendBy);
    int zeroExtendedX = yices_zero_extend(x, extendBy);

    assertThat(yices_term_to_string(x)).isNotNull();
    assertThat(yices_term_num_children(x)).isEqualTo(0);
    assertThat(yices_term_num_children(signExtendedX)).isEqualTo(initialSize + extendBy);
    assertThat(yices_term_to_string(signExtendedX)).isNotNull();
    assertThat(yices_term_num_children(zeroExtendedX)).isEqualTo(initialSize + extendBy);
    assertThat(yices_term_to_string(zeroExtendedX)).isNotNull();

    int bvSignExt = yices_proj_arg(yices_term_child(signExtendedX, 0));
    int bvSizeSignExt = yices_term_bitsize(bvSignExt);
    int extendedBySignExt = yices_term_num_children(signExtendedX) - bvSizeSignExt;
    assertThat(extendedBySignExt).isEqualTo(extendBy);

    int bvZeroExt = yices_proj_arg(yices_term_child(zeroExtendedX, 0));
    int bvSizeZeroExt = yices_term_bitsize(bvZeroExt);
    int extendedByZeroExt = yices_term_num_children(zeroExtendedX) - bvSizeZeroExt;
    assertThat(extendedByZeroExt).isEqualTo(extendBy);

    assertThat(yices_term_child(zeroExtendedX, bvSizeZeroExt)).isEqualTo(yices_false());
    assertThat(yices_term_child(signExtendedX, bvSizeSignExt)).isNotEqualTo(yices_false());

    yices_proj_arg(yices_term_child(x, 0)); // throws
  }

  @Test
  public void booleanParse() {
    int test = yices_parse_term("false");
    assertThat(yices_false()).isEqualTo(test);
    int test2 = yices_parse_term("true");
    assertThat(yices_true()).isEqualTo(test2);
  }

  @Test
  public void bvSum() {
    int type = yices_bv_type(5);
    int bv1 = yices_named_variable(type, "x");
    int bv2 = yices_named_variable(type, "y");
    int add = yices_bvadd(bv1, bv2);
    int constructor = yices_term_constructor(add);
    assertThat(constructor).isEqualTo(YICES_BV_SUM);
  }

  @Test
  public void bvMul() {
    int type = yices_bv_type(5);
    int bv2 = yices_named_variable(type, "x");
    int mul = yices_bvmul(bv2, bv2);
    assertThat(yices_term_constructor(mul)).isEqualTo(YICES_POWER_PRODUCT);
    // bv2 + bv2 == bv2²
    int[] component = yices_product_component(mul, 0);
    assertThat(component[0]).isEqualTo(bv2);
    assertThat(component[1]).isEqualTo(2);
    assertThat(yices_term_constructor(yices_bvpower(component[0], component[1]))).isGreaterThan(0);
  }

  /**
   * Only to be used for tests in this class. Old implementation used for creating/retrieving named
   * variables. Superseded by Yices2FormulaCreator.createNamedVariable() for reasons outlined there.
   */
  private static int yices_named_variable(int type, String name) {
    int termFromName = yices_get_term_by_name(name);
    if (termFromName != -1) {
      int termFromNameType = yices_type_of_term(termFromName);
      if (type == termFromNameType) {
        return termFromName;
      } else {
        throw new IllegalArgumentException(
            String.format(
                "Can't create variable with name '%s' and type '%s' "
                    + "as it would omit a variable with type '%s'",
                name, yices_type_to_string(type), yices_type_to_string(termFromNameType)));
      }
    }
    int var = yices_new_uninterpreted_term(type);
    yices_set_term_name(var, name);
    return var;
  }
}
