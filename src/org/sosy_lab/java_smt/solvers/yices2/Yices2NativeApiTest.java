/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.yices2;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_SUM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_EQ_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_NOT_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_OR_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_RATIONAL;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_add;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_and;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_and2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_eq_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_gt_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_lt_atom;
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
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsum_component;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvxor2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_check_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_check_sat;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_context_disable_option;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_def_terms;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_eq;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_exit;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_false;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_model;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_term_name;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_idiv;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_iff;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_init;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int32;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int64;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_model_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_mul;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_named_variable;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_uninterpreted_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_not;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_or;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_or2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_bvbin;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_rational;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_proj_arg;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_push;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_rational32;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_real_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_redand;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_set_config_checked;
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
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_val_get_mpq;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_zero_extend;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import com.google.common.primitives.Ints;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.Model;

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
    yices_set_config_checked(cfg, "solver-type", "dpllt");
    yices_set_config_checked(cfg, "mode", "push-pop");
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
    int term_true = yices_true();
    int term_false = yices_false();
    int formula = yices_and2(term_true, term_false);
    yices_assert_formula(env, formula);
    assertEquals(UNSAT, yices_check_context(env, 0));
  }

  @Test
  public void simpleSAT() {
    int term_true = yices_true();
    int formula = yices_and2(term_true, term_true);
    yices_assert_formula(env, formula);
    assertEquals(SAT, yices_check_context(env, 0));
  }

  /*
   * 3=SAT 4=UNSAT
   */
  @Test
  public void arrayArgSAT() {
    int n = 4;
    int term_true = yices_true();
    int[] terms = {term_true, term_true, term_true, term_true};
    int formula = yices_and(n, terms);
    yices_assert_formula(env, formula);
    assertEquals(SAT, yices_check_context(env, 0));
  }

  @Test
  public void arrayArgUNSAT() {
    int n = 4;
    int term_true = yices_true();
    int term_false = yices_false();
    int[] terms = {term_false, term_true, term_true, term_true};
    int formula = yices_and(n, terms);
    yices_assert_formula(env, formula);
    assertEquals(UNSAT, yices_check_context(env, 0));
  }

  @Test
  public void arithAddSAT() {
    int one = yices_int32(1);
    int two = yices_int32(2);
    int three = yices_int32(3);
    int add = yices_add(one, two);
    int equal = yices_eq(three, add);
    yices_assert_formula(env, equal);
    assertEquals(SAT, yices_check_context(env, 0));
  }

  @Test
  public void arithAddUNSAT() {
    int one = yices_int32(1);
    int two = yices_int32(99);
    int three = yices_int32(3);
    int add = yices_add(one, two);
    int equal = yices_eq(three, add);
    yices_assert_formula(env, equal);
    assertEquals(UNSAT, yices_check_context(env, 0));
  }

  @Test(expected = IllegalArgumentException.class)
  public void rationalError() {
    int rat = yices_rational32(1, 0);
    System.out.println(rat); // "use" variable
  }

  @Test
  public void negativeRationalError() {
    // TODO negative unsigned integer causes no error. Need to ensure positive value before
    int rat = yices_rational32(1, -5);
    System.out.println(rat); // "use" variable
  }

  @Test(expected = IllegalArgumentException.class)
  public void wrongType() {
    int one = yices_int32(1);
    int bitsize = yices_term_bitsize(one);
    System.out.println(bitsize); // "use" variable
  }

  @Test
  public void testRange() {
    int intmax = yices_int32(Integer.MAX_VALUE);
    int longmax = yices_int64(Long.MAX_VALUE);
    int gt = yices_arith_gt_atom(longmax, intmax);
    yices_assert_formula(env, gt);
    assertEquals(SAT, yices_check_context(env, 0));
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
    assertEquals(SAT, yices_check_context(env, 0));
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
    assertEquals(UNSAT, yices_check_context(env, 0));
  }

  @Test
  public void boolValueQuery() {
    int v1 = yices_true();
    int v2 = yices_false();
    assertTrue(yices_bool_const_value(v1));
    assertFalse(yices_bool_const_value(v2));
  }

  @Test(expected = IllegalArgumentException.class)
  public void boolValueTypeMismatch() {
    int v1 = yices_int32(45);
    boolean constTerm = yices_bool_const_value(v1);
    System.out.println(constTerm);
  }

  @Test
  public void bitvectorReturn() {
    int bv1 = yices_parse_bvbin("111000");
    int[] bvComp = {0, 0, 0, 1, 1, 1};
    int bvsize = yices_term_bitsize(bv1);
    assertEquals(6, bvsize);
    int[] bvReturn = yices_bv_const_value(bv1, bvsize);
    assertTrue(Arrays.equals(bvComp, bvReturn));
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
    Yices2FormulaCreator creator = new Yices2FormulaCreator(env);
    assertEquals(creator.convertValue(ratConst, ratConst), Rational.of(num + "/" + den));
    assertEquals(creator.convertValue(bigConst, bigConst), largeNumber);
    assertEquals(
        creator.convertValue(negativeNumConst, negativeNumConst),
        Rational.of(negativeNum + "/" + den));
    assertEquals(
        creator.convertValue(negativeDenConst, negativeDenConst),
        Rational.of(num + "/" + negativeDen));
    assertEquals(
        creator.convertValue(negativeNumDenConst, negativeNumDenConst),
        Rational.of(negativeNum + "/" + negativeDen));
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
      assertEquals(BigInteger.valueOf(value), big);
    }
  }

  @Test
  public void termNaming() {
    int t = yices_parse_bvbin("0100100001100101011011000110110001101111");
    String termName = "Hello";
    yices_set_term_name(t, termName);
    assertEquals(yices_get_term_name(t), termName);
  }

  @Test
  public void satWithVariable() {
    int term_false = yices_false();
    int var = yices_new_uninterpreted_term(yices_bool_type());
    int formula = yices_or2(term_false, var);
    yices_assert_formula(env, formula);
    assertEquals(SAT, yices_check_context(env, 0));
  }

  // Yices converts add(YICES_ARITH_CONST, YICES_ARITH_CONST) to an YICES_ARITH_CONST
  // Yices converts add(YICES_ARITH_CONST, YICES_UNINTERPRETED_TERM) to YICES_ARITH_SUM
  @Test
  public void termConstructorAdd() {
    int one = yices_int32(1);
    int two = yices_new_uninterpreted_term(yices_int_type()); // yices_int32(2);
    int addition = yices_add(one, two);
    assertEquals(41, YICES_ARITH_SUM);
    assertEquals(YICES_ARITH_SUM, yices_term_constructor(addition));
  }

  @Test
  public void termConstructorAnd() {
    // and 1 2 is replaced with not (or (not 1) (not 2))
    int Btrue = yices_new_uninterpreted_term(yices_bool_type()); // yices_true();
    yices_set_term_name(Btrue, "Btrue");
    int Btwo = yices_new_uninterpreted_term(yices_bool_type());
    yices_set_term_name(Btwo, "Btwo");
    int and = yices_and2(Btrue, Btwo);
    int children = yices_term_num_children(and);
    int child = yices_term_child(and, 0);
    assertEquals(YICES_OR_TERM, yices_term_constructor(child));
    children = yices_term_num_children(child);
    assertEquals(2, children);
    assertEquals("(and Btrue Btwo)", yices_term_to_string(and));
    assertEquals(YICES_NOT_TERM, yices_term_constructor(and));
  }

  @Test
  public void termConstructorOr() {
    int Bfalse = yices_new_uninterpreted_term(yices_bool_type()); // yices_false();
    // yices_set_term_name(Bfalse, "1");
    int two = yices_new_uninterpreted_term(yices_bool_type());
    // yices_set_term_name(two, "5");
    int[] orArray = {Bfalse, two, Bfalse, Bfalse};
    int or = yices_or(4, orArray);
    assertTrue(yices_term_is_bool(or));
    assertEquals(YICES_OR_TERM, yices_term_constructor(or));
    // Works after changing something?
  } // Expecting YICES_OR_TERM as constructor but getting YICES_UNINTERPRETED_TERM

  @Test
  public void termConstructorNot() {
    int Btrue = yices_new_uninterpreted_term(yices_bool_type()); // yices_true();
    yices_set_term_name(Btrue, "Btrue");
    int Btwo = yices_new_uninterpreted_term(yices_bool_type());
    yices_set_term_name(Btwo, "Btwo");
    int not = yices_not(Btrue);
    assertEquals(YICES_NOT_TERM, yices_term_constructor(not));
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
    assertEquals(yices_true(), eq);
  }

  @Test
  public void orSimplification() {
    int bTrue = yices_true();
    int boolType = yices_bool_type();
    int[] orArray = new int[20];
    for (int i = 0; i < (orArray.length - 1); i++) {
      orArray[i] = yices_named_variable(boolType, "x" + i);
    }
    orArray[(orArray.length - 1)] = bTrue;
    int or = yices_or(orArray.length, orArray);
    assertEquals(yices_true(), or);
  }

  @Test
  public void andSimplification() {
    int bFalse = yices_false();
    int boolType = yices_bool_type();
    int[] andArray = new int[20];
    for (int i = 0; i < (andArray.length - 1); i++) {
      andArray[i] = yices_named_variable(boolType, "x" + i);
    }
    andArray[(andArray.length - 1)] = bFalse;
    int and = yices_and(andArray.length, andArray);
    assertEquals(yices_false(), and);
  }

  @Test
  public void iffConstructor() {
    int one = yices_new_uninterpreted_term(yices_bool_type());
    int two = yices_new_uninterpreted_term(yices_bool_type());
    int iff = yices_iff(one, two);
    assertEquals(YICES_EQ_TERM, yices_term_constructor(iff));
  }

  @SuppressWarnings("resource")
  @Test
  public void modelTest() {
    int varx = yices_named_variable(yices_real_type(), "x");
    int eq = yices_arith_eq_atom(varx, yices_int32(10));
    int query = yices_named_variable(yices_real_type(), "x");
    Yices2FormulaCreator creator = new Yices2FormulaCreator(env);
    yices_push(env);
    yices_assert_formula(env, eq);
    System.out.println("varx: " + varx);
    System.out.println("query: " + query);
    if (yices_check_sat(env, 0)) {
      Model m = new Yices2Model(yices_get_model(env, 1), creator);
      Object val = m.evaluate(creator.encapsulateWithTypeOf(varx));
      System.out.println(val);
      m.close();
    }
  }

  @SuppressWarnings("resource")
  @Test
  public void modelExplorationTest() {
    int x = yices_int32(5);
    int y = yices_int32(7);
    int z = yices_named_variable(yices_int_type(), "z");
    int gt = yices_arith_gt_atom(z, x);
    int lt = yices_arith_lt_atom(z, y);
    int x2 = yices_int32(333);
    int y2 = yices_int32(335);
    int z2 = yices_named_variable(yices_int_type(), "z2");
    int gt2 = yices_arith_gt_atom(z2, x2);
    int lt2 = yices_arith_lt_atom(z2, y2);
    int sub = yices_sub(z2, z);
    int eq = yices_arith_eq_atom(sub, yices_int32(328));
    Yices2FormulaCreator creator = new Yices2FormulaCreator(env);
    yices_push(env);
    yices_assert_formula(env, gt);
    yices_assert_formula(env, lt);
    yices_assert_formula(env, gt2);
    yices_assert_formula(env, lt2);
    yices_assert_formula(env, eq);
    if (yices_check_sat(env, 0)) {
      long model = yices_get_model(env, 1);
      Model m = new Yices2Model(model, creator);
      System.out.println(yices_model_to_string(model));
      Object val = m.evaluate(creator.encapsulateWithTypeOf(eq));
      System.out.println(val);
      int addT = yices_add(z, z2);
      Object val2 = m.evaluate(creator.encapsulateWithTypeOf(addT));
      System.out.println(val2);
      System.out.println("DEFINED TERMS");
      int[] terms = yices_def_terms(model);
      for (int i = 0; i < terms.length; i++) {
        System.out.println(yices_term_to_string(terms[i]));
        System.out.println("Term id is: " + terms[i]);
        int[] yval = yices_get_value(model, terms[i]);
        System.out.println("Node id is: " + yval[0]);
        System.out.println("Node tag is: " + yval[1]);
        if (yval[1] == YVAL_RATIONAL) {
          System.out.println("Value is: " + yices_val_get_mpq(model, yval[0], yval[1]));
        }
      }
      m.close();
    } else {
      throw new IllegalArgumentException("The environment is not solvable!");
    }
  }

  @Test
  public void parseTerm() {
    // int x = yices_parse_term("define x::int");
    // int y = yices_parse_term("define y::int");
    // int xsmallery = yices_parse_term("assert (< x y)");
    // int xbigger4 = yices_parse_term("assert (> x 4)");
    // int ysmaller7 = yices_parse_term("assert (< y 7)");
    // assertEquals(yices_check_context(env, 0), SAT);
    int y = yices_int32(5);
    yices_set_term_name(y, "y");
    int x = yices_parse_term("(/= y 5)");
    assertEquals("false", yices_term_to_string(x));
  }

  @Test
  public void arithSimplification() {
    int x = yices_int32(6);
    int y = yices_int32(7);
    int add = yices_add(x, y);
    int mul = yices_mul(x, y);
    Yices2FormulaCreator creator = new Yices2FormulaCreator(env);
    assertEquals(BigInteger.valueOf(13), creator.convertValue(add, add));
    assertEquals(YICES_ARITH_CONST, yices_term_constructor(add));
    assertEquals(BigInteger.valueOf(42), creator.convertValue(mul, mul));
    assertEquals(YICES_ARITH_CONST, yices_term_constructor(mul));
  }

  @Test
  public void sumComponents() {
    int three = yices_int32(3);
    int rat = yices_parse_rational("3/2");
    int x = yices_named_variable(yices_int_type(), "x");
    int[] oneX = {three, x};
    int sumOneX = yices_sum(2, oneX);
    for (int i = 0; i < yices_term_num_children(sumOneX); i++) {
      System.out.println(yices_term_to_string(sumOneX));
      System.out.println(yices_sum_component(sumOneX, i));
    }
    int[] twoX = {three, x, x};
    int sumTwoX = yices_sum(3, twoX);
    for (int i = 0; i < yices_term_num_children(sumTwoX); i++) {
      System.out.println(yices_term_to_string(sumTwoX));
      System.out.println(yices_sum_component(sumTwoX, i));
    }
    int[] twoThrees = {three, x, three};
    int sumTwoThrees = yices_sum(3, twoThrees);
    for (int i = 0; i < yices_term_num_children(sumTwoThrees); i++) {
      System.out.println(yices_term_to_string(sumTwoThrees));
      System.out.println(yices_sum_component(sumTwoThrees, i));
    }
    int xTimesRational = yices_mul(rat, x);
    int[] ratSum = {three, xTimesRational};
    int sumRatX = yices_sum(2, ratSum);
    for (int i = 0; i < yices_term_num_children(sumRatX); i++) {
      System.out.println(yices_term_to_string(sumRatX));
      System.out.println(yices_sum_component(sumRatX, i));
    }
  }

  @Test
  public void bvSumComponents() {
    int bv1 = yices_parse_bvbin("00101");
    int bv5type = yices_bv_type(5);
    int x = yices_named_variable(bv5type, "x");
    int negativeX = yices_bvmul(yices_bvconst_minus_one(5), x);
    int add = yices_bvadd(bv1, negativeX);
    for (int i = 0; i < yices_term_num_children(add); i++) {
      System.out.println(yices_term_to_string(add));
      int[] component = yices_bvsum_component(add, i, yices_term_bitsize(add));
      String value =
          Joiner.on("")
              .join(
                  Lists.reverse(
                      Ints.asList(Arrays.copyOfRange(component, 0, component.length - 1))));
      int term = component[component.length - 1];
      System.out.println("Value of coefficient: " + value);
      System.out.println("Coefficient as BigInt: " + new BigInteger(value, 2));
      System.out.println("Term id: " + term);
    }
  }

  @Test
  public void bvExtensionStructureTest() {
    int extendBy = 5;
    int x = yices_named_variable(yices_bv_type(5), "x");
    List<Integer> terms = new ArrayList<Integer>();
    terms.add(yices_sign_extend(x, extendBy));
    terms.add(yices_sign_extend(x, extendBy));
    terms.add(yices_zero_extend(x, extendBy));
    terms.add(yices_zero_extend(x, extendBy));
    for (int t : terms) {
      System.out.println("--------BEGIN-------");
      System.out.println(yices_term_to_string(t));
      for (int i = 0; i < yices_term_num_children(t); i++) {
        System.out.println(yices_term_to_string(yices_term_child(t, i)));
      }
      int bv = yices_proj_arg(yices_term_child(t, 0));
      int bvSize = yices_term_bitsize(bv);
      int extendedBy = yices_term_num_children(t) - bvSize;
      System.out.println("Extended by: " + extendedBy);
      if (extendedBy != 0) {
        if (yices_term_child(t, bvSize) == yices_false()) {
          System.out.println("Zero-Extend");
        } else {
          System.out.println("Sign-extend");
        }
      }
      System.out.println("--------END-------");
    }
  }

  @Test
  public void booleanParse() {
    int test = yices_parse_term("false");
    assertEquals(yices_false(), test);
    int test2 = yices_parse_term("true");
    assertEquals(yices_true(), test2);
  }
}
