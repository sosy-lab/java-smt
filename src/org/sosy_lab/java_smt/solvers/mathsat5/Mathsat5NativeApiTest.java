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
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_integer_type;
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
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_pop_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_push_backtrack_point;
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
}
