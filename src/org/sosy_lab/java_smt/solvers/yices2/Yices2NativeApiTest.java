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
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_SUM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_OR_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_add;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_and;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_and2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_gt_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_assert_formula;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bool_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bool_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bv_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvand2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvconst_one;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bveq_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvxor2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_check_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_context_disable_option;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_eq;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_exit;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_false;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_major_version;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_patch_level;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_term_name;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_version;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_init;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int32;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int64;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_new_uninterpreted_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_or;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_or2;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_bvbin;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_rational32;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_redand;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_set_config;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_set_term_name;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_bitsize;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_child;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_constructor;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_is_bool;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_num_children;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_true;

import java.util.Arrays;
import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;

@SuppressWarnings({"unused"})
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
  public void checkVersion() {
    int version = yices_get_version();
    assertEquals(2, version);
    int majorVersion = yices_get_major_version();
    assertEquals(6, majorVersion);
    int patchlevel = yices_get_patch_level();
    assertEquals(1, patchlevel);
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
    int term_false = yices_false();
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
    int error = yices_rational32(1, 0);
  }

  @Test
  public void negativeRationalError() {
    // TODO negative unsigned integer causes no error. Need to ensure positive value before
    int error = yices_rational32(1, -5);
  }

  @Test(expected = IllegalArgumentException.class)
  public void wrongType() {
    int one = yices_int32(1);
    int error = yices_term_bitsize(one);
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
    yices_bool_const_value(v1);
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
    int two = yices_new_uninterpreted_term(yices_int_type());// yices_int32(2);
    int addition = yices_add(one, two);
    assertEquals(41, YICES_ARITH_SUM);
    assertEquals(yices_term_constructor(addition), YICES_ARITH_SUM);
  }

  @Test
  public void termConstructorAnd() {
    int Btrue = yices_new_uninterpreted_term(yices_bool_type());// yices_true();
    int Btwo = yices_new_uninterpreted_term(yices_bool_type());
    int and = yices_and2(Btrue, Btwo);
    if (yices_term_num_children(and) > 0) {
      int fun = yices_term_child(and, 0);
      assertEquals(yices_term_constructor(fun), -1);
    }
    assertEquals(yices_term_constructor(and), -1);
    /*
     * There is no Value for a YICES_AND_TERM If Btrue and two are both uninterpreted terms
     * term_constructor is YICES_OR_TERM? If Btrue is yices_true() and Btwo is uninterpreted_term
     * Result is UNINTERPRETED_TERM --> Likely simplified as Result is only dependent on Btwo
     */

    // Result is YICES_UNINTERPRETED_TERM. But normal variables are also UNINTERPRETED_TERM
  }

  @Test
  public void termConstructorOr() {
    int Bfalse = yices_new_uninterpreted_term(yices_bool_type());// yices_false();
    int two = yices_new_uninterpreted_term(yices_bool_type());
    int[] orArray = {Bfalse, two, Bfalse, Bfalse};
    int or = yices_or(4, orArray);
    assertTrue(yices_term_is_bool(or));
    if (yices_term_num_children(or) > 0) {
      // Testing if it is a function with children (or Bfalse two)
      int fun = yices_term_child(or, 0);
      assertEquals(yices_term_constructor(fun), -1);
    }
    assertEquals(yices_term_constructor(or), YICES_OR_TERM);
  } // Expecting YICES_OR_TERM as constructor but getting YICES_UNINTERPRETED_TERM


}
