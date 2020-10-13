// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static com.google.common.truth.Truth.assertThat;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_assert_formula;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_check_sat;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_config;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_config;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_model_iterator;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_from_smtlib2;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_integer_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_model;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_rational_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_asin;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_eq;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_equal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_exp;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_log;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_not;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_pi;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_pow;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_sin;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_times;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_variable;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_model_create_iterator;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_model_iterator_has_next;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_model_iterator_next;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_pop_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_push_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_set_option_checked;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_is_pi;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_type_equals;

import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.api.SolverException;

public class Mathsat5NativeApiTest extends Mathsat5AbstractNativeApiTest {

  private long const0;
  private long const1;
  private long var;

  @BeforeClass
  public static void loadMathsat() {
    try {
      NativeLibraries.loadLibrary("mathsat5j");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("MathSAT5 is not available", e);
    }
  }

  @Before
  public void createEnvironment() {
    long cfg = msat_create_config();

    msat_set_option_checked(cfg, "model_generation", "true");
    // msat_set_option_checked(cfg, "theory.la.split_rat_eq", "false");

    env = msat_create_env(cfg);
    msat_destroy_config(cfg);

    const0 = msat_make_number(env, "0");
    const1 = msat_make_number(env, "1");
    long rationalType = msat_get_rational_type(env);
    var = msat_make_variable(env, "rat", rationalType);
  }

  /** x == 0 and sin(x) == 0 SAT; x == 1 and sin(x) == 0 UNSAT. */
  @Test
  public void sinTest() throws IllegalStateException, InterruptedException, SolverException {
    long sin = msat_make_sin(env, var);

    msat_push_backtrack_point(env);

    msat_assert_formula(env, msat_make_equal(env, var, const0));
    msat_assert_formula(env, msat_make_equal(env, sin, const0));

    assertThat(msat_check_sat(env)).isTrue();

    msat_pop_backtrack_point(env);

    msat_assert_formula(env, msat_make_equal(env, var, const1));
    msat_assert_formula(env, msat_make_equal(env, sin, const0));

    assertThat(msat_check_sat(env)).isFalse();
  }

  /** x == 0 and e^x = 1 SAT; x == 1 and e^x == 1 UNSAT. */
  @Test
  public void expTest() throws IllegalStateException, InterruptedException, SolverException {
    long exp = msat_make_exp(env, var);

    msat_push_backtrack_point(env);

    msat_assert_formula(env, msat_make_equal(env, var, const0));
    msat_assert_formula(env, msat_make_equal(env, exp, const1));

    assertThat(msat_check_sat(env)).isTrue();

    msat_pop_backtrack_point(env);

    msat_assert_formula(env, msat_make_equal(env, var, const1));
    msat_assert_formula(env, msat_make_equal(env, exp, const1));

    assertThat(msat_check_sat(env)).isFalse();
  }

  /**
   * Testing is_pi(x) and x == pi true (Works); Tried x == pi and sin(x) == 0 SAT but solver
   * calculates endlessly.
   */
  @Ignore
  public void piTest() throws IllegalStateException, InterruptedException, SolverException {
    long pi = msat_make_pi(env);
    long sin = msat_make_sin(env, var);

    assertThat(msat_term_is_pi(env, pi)).isTrue();
    assertThat(msat_term_is_pi(env, const0)).isFalse();

    msat_assert_formula(env, msat_make_eq(env, sin, const0));
    msat_assert_formula(env, msat_make_eq(env, var, pi));

    assertThat(msat_check_sat(env)).isTrue();
  }

  /** Similar problem as sin(pi); Calculates endlessly (even asin(0) == 0). */
  @Ignore
  public void asinTest() throws IllegalStateException, InterruptedException, SolverException {
    long asin = msat_make_asin(env, var);

    msat_push_backtrack_point(env);

    msat_assert_formula(env, msat_make_equal(env, var, const0));
    msat_assert_formula(env, msat_make_equal(env, asin, const0));

    assertThat(msat_check_sat(env)).isTrue();

    msat_pop_backtrack_point(env);

    msat_assert_formula(env, msat_make_equal(env, var, const1));
    msat_assert_formula(env, msat_make_equal(env, asin, const0));

    assertThat(msat_check_sat(env)).isFalse();
  }

  /**
   * log(term) == natural log of term Similar problem as asin; Calculates endlessly even with
   * trivial formulas as ln(1) == 0 or log(e^1) == 1.
   */
  @Ignore
  public void logTest() throws IllegalStateException, InterruptedException, SolverException {
    // exp(1) == e
    long logE = msat_make_log(env, msat_make_exp(env, var));
    long logVar = msat_make_log(env, var);

    msat_push_backtrack_point(env);

    msat_assert_formula(env, msat_make_equal(env, var, const1));
    msat_assert_formula(env, msat_make_equal(env, logVar, const0));

    assertThat(msat_check_sat(env)).isTrue();

    msat_pop_backtrack_point(env);
    msat_push_backtrack_point(env);

    msat_assert_formula(env, msat_make_equal(env, var, const1));
    msat_assert_formula(env, msat_make_equal(env, logE, const1));

    assertThat(msat_check_sat(env)).isTrue();

    msat_pop_backtrack_point(env);

    msat_assert_formula(env, msat_make_equal(env, var, const1));
    msat_assert_formula(env, msat_make_equal(env, logVar, const1));

    assertThat(msat_check_sat(env)).isFalse();
  }

  /**
   * First we test: var * var == var ^ 2 && var != 1 because 1*1*1*1... == 1 && var != 0 after that
   * we test: var * var != var ^ 3 && var != 1 && var != 0.
   */
  @Test
  public void powTest() throws IllegalStateException, InterruptedException, SolverException {
    long const2 = msat_make_number(env, "2");
    long const3 = msat_make_number(env, "3");

    long pow2 = msat_make_pow(env, var, const2);
    long pow3 = msat_make_pow(env, var, const3);
    long mult2 = msat_make_times(env, var, var);

    msat_assert_formula(
        env, msat_make_not(env, msat_make_equal(env, var, msat_make_number(env, "1"))));
    msat_assert_formula(
        env, msat_make_not(env, msat_make_equal(env, var, msat_make_number(env, "0"))));

    msat_push_backtrack_point(env);

    msat_assert_formula(env, msat_make_equal(env, pow2, mult2));

    assertThat(msat_check_sat(env)).isTrue();

    msat_pop_backtrack_point(env);

    msat_assert_formula(env, msat_make_equal(env, pow3, mult2));

    assertThat(msat_check_sat(env)).isFalse();
  }

  @Test
  public void typeTest() throws IllegalStateException {

    long const2 = msat_make_number(env, "2");
    long const3 = msat_make_number(env, "3");

    long i = msat_make_variable(env, "i", msat_get_integer_type(env));
    long r = msat_make_variable(env, "r", msat_get_rational_type(env));

    checkRationalType(msat_make_pi(env));
    checkRationalType(msat_make_sin(env, r));
    checkRationalType(msat_make_exp(env, r));
    checkRationalType(msat_make_asin(env, r));
    checkRationalType(msat_make_log(env, msat_make_exp(env, r)));
    checkRationalType(msat_make_log(env, r));

    checkRationalType(msat_make_pi(env));
    checkRationalType(msat_make_sin(env, i));
    checkRationalType(msat_make_exp(env, i));
    checkRationalType(msat_make_asin(env, i));
    checkRationalType(msat_make_log(env, msat_make_exp(env, i)));
    checkRationalType(msat_make_log(env, i));

    checkRationalType(msat_make_pow(env, r, const2));
    checkRationalType(msat_make_pow(env, r, const3));
    checkRationalType(msat_make_times(env, r, r));

    checkIntegerType(msat_make_pow(env, i, const2));
    checkIntegerType(msat_make_pow(env, i, const3));
    checkIntegerType(msat_make_times(env, i, i));

    checkRationalType(msat_make_pow(env, i, i));
    checkRationalType(msat_make_times(env, i, r));

    checkRationalType(msat_make_pow(env, r, r));
    checkRationalType(msat_make_times(env, r, r));
  }

  private void checkRationalType(long term) {
    assertThat(msat_type_equals(msat_term_get_type(term), msat_get_rational_type(env))).isTrue();
  }

  private void checkIntegerType(long term) {
    assertThat(msat_type_equals(msat_term_get_type(term), msat_get_integer_type(env))).isTrue();
  }

  private static final String QUERY =
      "(declare-fun __VERIFIER_nondet_int!2@ () Int)"
          + "(declare-fun |main::length@3| () Int)"
          + "(declare-fun |__ADDRESS_OF___VERIFIER_successful_alloc_*void#1@| () Int)"
          + "(declare-fun |main::arr@3| () Int)"
          + "(declare-fun |main::a@2| () Int)"
          + "(declare-fun *int@1 () (Array Int Int))"
          + "(declare-fun *int@2 () (Array Int Int))"
          + "(declare-fun |main::__CPAchecker_TMP_0@2| () Int)"
          + "(declare-fun |main::a@3| () Int)"
          + "(define-fun v8 () Int 0)"
          + "(define-fun v13 () Int 4)"
          + "(define-fun v14 () Int __VERIFIER_nondet_int!2@)"
          + "(define-fun v15 () Int |main::length@3|)"
          + "(define-fun v16 () Bool (= v14 v15))"
          + "(define-fun v17 () Int 1)"
          + "(define-fun v18 () Bool (<= v17 v15))"
          + "(define-fun v22 () Bool (and v16 v18))"
          + "(define-fun v30 () Int |__ADDRESS_OF___VERIFIER_successful_alloc_*void#1@|)"
          + "(define-fun v31 () Bool (<= v30 v8))"
          + "(define-fun v32 () Bool (not v31))"
          + "(define-fun v33 () Bool ((_ divisible 4) (- v30 v8)))"
          + "(define-fun v35 () Int (- 4))"
          + "(define-fun v36 () Bool (<= v30 v35))"
          + "(define-fun v37 () Bool (not v36))"
          + "(define-fun v41 () Int |main::arr@3|)"
          + "(define-fun v42 () Bool (= v30 v41))"
          + "(define-fun v43 () Bool (and v32 v33))"
          + "(define-fun v44 () Bool (and v37 v43))"
          + "(define-fun v48 () Bool (= v41 v8))"
          + "(define-fun v51 () Bool (not v48))"
          + "(define-fun v54 () Int (- 1))"
          + "(define-fun v56 () Int |main::a@2|)"
          + "(define-fun v57 () Int (* v54 v56))"
          + "(define-fun v58 () Int (+ v41 v57))"
          + "(define-fun v2300 () (Array Int Int) *int@1)"
          + "(define-fun v2304 () (Array Int Int) *int@2)"
          + "(define-fun v6120 () Int (select v2300 v56))"
          + "(define-fun v6121 () Int (select v2300 v41))"
          + "(define-fun v6122 () Bool (= v6120 v6121))"
          + "(define-fun v6123 () Bool (not v6122))"
          + "(define-fun v6135 () Int |main::__CPAchecker_TMP_0@2|)"
          + "(define-fun v6136 () Bool (= v56 v6135))"
          + "(define-fun v6139 () Int |main::a@3|)"
          + "(define-fun v6140 () Int (* v54 v6139))"
          + "(define-fun v6141 () Int (+ v56 v6140))"
          + "(define-fun v6142 () Bool (= v6141 v13))"
          + "(define-fun v6144 () Int (+ v6120 v6121))"
          + "(define-fun v6145 () (Array Int Int) (store v2300 v56 v6144))"
          + "(define-fun v6146 () Bool (= v2304 v6145))"
          + "(define-fun v18733 () Int (* v13 v15))"
          + "(define-fun v18735 () Int (+ v18733 v30))"
          + "(define-fun v18736 () Bool (<= v18735 v8))"
          + "(define-fun v18737 () Bool (not v18736))"
          + "(define-fun v18738 () Bool (and v44 v18737))"
          + "(define-fun v18739 () Bool (and v42 v18738))"
          + "(define-fun v18740 () Bool (and v22 v18739))"
          + "(define-fun v18741 () Bool (and v51 v18740))"
          + "(define-fun v18744 () Int (+ v18733 v58))"
          + "(define-fun v18745 () Bool (= v18744 v13))"
          + "(define-fun v18746 () Bool (and v18741 v18745))"
          + "(define-fun v18747 () Bool (and v6123 v18746))"
          + "(define-fun v18748 () Bool (and v6146 v18747))"
          + "(define-fun v18749 () Bool (and v6136 v18748))"
          + "(define-fun v18750 () Bool (and v6142 v18749))"
          + "(assert v18750)";

  // TODO The next method crashes with MathSAT5 version 5.6.4
  // (NullPointer during iterator creation).
  // The bug is reported, we need to check this with the next release.
  @Ignore
  public void modelIteratorCrash()
      throws IllegalStateException, InterruptedException, SolverException {

    long parsedFormula = msat_from_smtlib2(env, QUERY);
    msat_assert_formula(env, parsedFormula);

    boolean isSat = msat_check_sat(env);
    assertThat(isSat).isTrue();

    long model = msat_get_model(env);
    long iter = msat_model_create_iterator(model);
    while (msat_model_iterator_has_next(iter)) {
      long[] key = new long[1];
      long[] value = new long[1];
      // System.out.println("before crash");
      @SuppressWarnings("unused")
      boolean check = msat_model_iterator_next(iter, key, value); // crash here
      // System.out.println(" " + check);
      // String k = msat_term_repr(key[0]);
      // System.out.println("after crash");
      // String v = msat_term_repr(value[0]);
      // System.out.println(k + " := " + v);
    }
    msat_destroy_model_iterator(iter);
  }

  private static final String LARGE_NUMBER_QUERY =
      "(declare-fun a () Int) (assert (= a 10000000000000000000000001))";

  @Test
  public void invalidLargeNumberInModelTest()
      throws IllegalStateException, InterruptedException, SolverException {
    long parsed = msat_from_smtlib2(env, LARGE_NUMBER_QUERY);
    msat_assert_formula(env, parsed);
    boolean isSat = msat_check_sat(env);
    assertThat(isSat).isTrue();

    long model = msat_get_model(env);
    long iter = msat_model_create_iterator(model);
    while (msat_model_iterator_has_next(iter)) {
      long[] key = new long[1];
      long[] value = new long[1];
      // System.out.println("before crash");
      @SuppressWarnings("unused")
      boolean check = msat_model_iterator_next(iter, key, value); // crash here
      // System.out.println(" " + check);
      // String k = msat_term_repr(key[0]);
      // System.out.println("after crash");
      // String v = msat_term_repr(value[0]);
      // System.out.println(k + " := " + v);
    }
    msat_destroy_model_iterator(iter);
  }
}
