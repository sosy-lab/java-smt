// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_assert_formula;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_check_sat;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_declare_function;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_bv_type_size;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_fp_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_fp_type_exp_width;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_fp_type_mant_width;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_integer_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_is_bv_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_constant;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_equal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_int_modular_congruence;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_pop_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_push_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_repr;

import org.junit.After;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.java_smt.api.SolverException;

@Ignore("prevent this abstract class being executed as testcase by ant")
public abstract class Mathsat5AbstractNativeApiTest {

  protected long env;

  @After
  public void freeEnvironment() {
    msat_destroy_env(env);
  }

  @Test
  public void bvSize() {
    long number = msat_make_bv_number(env, "42", 32, 10);
    long type = msat_term_get_type(number);

    assertThat(msat_is_bv_type(env, type)).isTrue();
    assertThat(msat_get_bv_type_size(env, type)).isEqualTo(32);

    long funcDecl = msat_declare_function(env, "testVar", type);
    long var = msat_make_constant(env, funcDecl);
    type = msat_term_get_type(var);

    assertThat(msat_is_bv_type(env, type)).isTrue();
    assertThat(msat_get_bv_type_size(env, type)).isEqualTo(32);
  }

  @Test
  public void fpExpWidth() {
    long type = msat_get_fp_type(env, 8, 23);
    assertThat(msat_get_fp_type_exp_width(env, type)).isEqualTo(8);
  }

  @Test
  public void fpMantWidth() {
    long type = msat_get_fp_type(env, 8, 23);
    assertThat(msat_get_fp_type_mant_width(env, type)).isEqualTo(23);
  }

  @Test
  public void fpExpWidthIllegal() {
    long type = msat_get_integer_type(env);
    assertThrows(IllegalArgumentException.class, () -> msat_get_fp_type_exp_width(env, type));
  }

  @Test
  public void modularCongruence()
      throws InterruptedException, IllegalStateException, SolverException {
    long type = msat_get_integer_type(env);

    long v1 = msat_declare_function(env, "v1", type);
    long t1 = msat_make_constant(env, v1);
    long v2 = msat_declare_function(env, "v2", type);
    long t2 = msat_make_constant(env, v2);

    long t = msat_make_int_modular_congruence(env, "42", t1, t2);

    assertThat(msat_term_repr(t)).isEqualTo("(`int_mod_congr_42` (`+_int` v1 (`*_int` -1 v2)) 0)");

    msat_assert_formula(env, t);

    msat_push_backtrack_point(env);
    msat_assert_formula(env, msat_make_equal(env, t1, msat_make_number(env, "3")));
    msat_assert_formula(env, msat_make_equal(env, t2, msat_make_number(env, "45")));
    assertThat(msat_check_sat(env)).isTrue(); // 3 == 45 mod 42
    msat_pop_backtrack_point(env);

    msat_push_backtrack_point(env);
    msat_assert_formula(env, msat_make_equal(env, t1, msat_make_number(env, "45")));
    msat_assert_formula(env, msat_make_equal(env, t2, msat_make_number(env, "45")));
    assertThat(msat_check_sat(env)).isTrue(); // 45 == 45 mod 42 according to Mathsat
    msat_pop_backtrack_point(env);

    msat_push_backtrack_point(env);
    msat_assert_formula(env, msat_make_equal(env, t1, msat_make_number(env, "87")));
    msat_assert_formula(env, msat_make_equal(env, t2, msat_make_number(env, "45")));
    assertThat(msat_check_sat(env)).isTrue(); // 87 == 45 mod 42 according to Mathsat
    msat_pop_backtrack_point(env);

    msat_push_backtrack_point(env);
    msat_assert_formula(env, msat_make_equal(env, t1, msat_make_number(env, "4")));
    msat_assert_formula(env, msat_make_equal(env, t2, msat_make_number(env, "45")));
    assertThat(msat_check_sat(env)).isFalse(); // 4 != 45 mod 42
    msat_pop_backtrack_point(env);
  }
}
