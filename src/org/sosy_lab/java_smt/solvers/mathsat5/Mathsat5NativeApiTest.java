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
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_config;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_create_shared_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_decl_get_arity;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_decl_get_name;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_config;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_model_iterator;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_proof_manager;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_from_smtlib2;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_bv_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_enum_constants;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_enum_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_integer_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_model;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_model_value;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_proof;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_proof_manager;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_rational_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_is_enum_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_is_integer_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_asin;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_extract;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_lshl;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_or;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_zext;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_eq;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_equal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_exp;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_false;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_log;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_not;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_pi;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_pow;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_sin;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_term;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_times;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_variable;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_model_create_iterator;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_model_iterator_has_next;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_model_iterator_next;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_pop_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_proof_get_arity;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_proof_get_child;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_proof_get_name;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_proof_id;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_proof_is_term;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_push_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_set_option_checked;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_is_pi;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_repr;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_type_equals;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_type_repr;

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
      Mathsat5SolverContext.loadLibrary(NativeLibraries::loadLibrary);
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

  @Test
  public void proofTest() throws SolverException, InterruptedException {
    long cfg = msat_create_config();

    msat_set_option_checked(cfg, "proof_generation", "true");

    env = msat_create_env(cfg);
    msat_destroy_config(cfg);

    testProofManager(env);
  }

  // Tests if it is possible to enable proof generation in a shared environment after it was not
  // enabled in the original
  @Test
  public void proofSharedEnvironmentTest() throws SolverException, InterruptedException {
    long cfg = msat_create_config();
    env = msat_create_env(cfg);
    msat_destroy_config(cfg);

    cfg = msat_create_config();
    msat_set_option_checked(cfg, "proof_generation", "true");
    long sharedEnv = msat_create_shared_env(cfg, env);
    msat_destroy_config(cfg);

    testProofManager(sharedEnv);
  }

  // MathSAT5 can not produce a msat_manager because there is no proof in this case. See
  // ProverEnvironmentTest class
  @SuppressWarnings("CheckReturnValue")
  @Test
  public void testProofOfFalse() throws SolverException, InterruptedException {
    long cfg = msat_create_config();
    msat_set_option_checked(cfg, "proof_generation", "true");
    env = msat_create_env(cfg);
    msat_destroy_config(cfg);

    long bottom = msat_make_false(env);
    msat_assert_formula(env, bottom);
    boolean isSat = msat_check_sat(env);
    assertThat(isSat).isFalse();

    assertThrows(IllegalArgumentException.class, () -> msat_get_proof_manager(env));
  }

  @Test
  public void apiExampleProofTest() throws SolverException, InterruptedException {

    long cfg = msat_create_config();
    msat_set_option_checked(cfg, "proof_generation", "true");
    msat_set_option_checked(cfg, "preprocessor.toplevel_propagation", "false");
    msat_set_option_checked(cfg, "preprocessor.simplification", "0");
    msat_set_option_checked(cfg, "theory.bv.eager", "false"); // for BV, only the lazy solver is

    msat_set_option_checked(cfg, "theory.fp.mode", "2");

    long localEnv = msat_create_env(cfg);
    msat_destroy_config(cfg);

    long f;

    String smtlib2 =
        "(declare-fun x1 () Real)"
            + "(declare-fun x2 () Real)"
            + "(declare-fun x3 () Real)"
            + "(declare-fun y1 () Real)"
            + "(declare-fun y2 () Real)"
            + "(declare-fun y3 () Real)"
            + "(declare-fun b () Real)"
            + "(declare-fun f (Real) Real)"
            + "(declare-fun g (Real) Real)"
            + "(declare-fun a () Bool)"
            + "(declare-fun c () Bool)"
            + "(assert (and a (= (+ (f y1) y2) y3) (<= y1 x1)))"
            + "(assert (and (= x2 (g b)) (= y2 (g b)) (<= x1 y1) (< x3 y3)))"
            + "(assert (= a (= (+ (f x1) x2) x3)))"
            + "(assert (and (or a c) (not c)))";
    f = msat_from_smtlib2(localEnv, smtlib2);

    msat_assert_formula(localEnv, f);

    boolean isSat = msat_check_sat(localEnv);

    assertThat(isSat).isFalse();

    long pm = msat_get_proof_manager(localEnv);

    long proof = msat_get_proof(pm);

    assertThat(msat_proof_is_term(proof)).isFalse();

    msat_destroy_proof_manager(pm);
    msat_destroy_env(localEnv);
  }

  // This test produces a SIGSEV, apparently because of the destruction of the proof, which is
  // needed an works without problem for other proofs.
  @Test
  @SuppressWarnings("unused")
  public void bitVectorProofTest() throws SolverException, InterruptedException {

    long cfg = msat_create_config();
    msat_set_option_checked(cfg, "proof_generation", "true");
    msat_set_option_checked(cfg, "theory.bv.eager", "false");
    env = msat_create_env(cfg);
    msat_destroy_config(cfg);

    long bv8 = msat_get_bv_type(env, 8);
    long bv32 = msat_get_bv_type(env, 32);

    // Constants
    long one32 = msat_make_bv_number(env, "1", 32, 10);
    long seven32 = msat_make_bv_number(env, "7", 32, 10);

    // Variables (unsigned char)
    long a = msat_make_variable(env, "char_a", bv8);
    long b = msat_make_variable(env, "char_b", bv8);

    // Extend to 32 bits (zero-extend) unsigned
    a = msat_make_bv_zext(env, 24, a);
    b = msat_make_bv_zext(env, 24, b);

    // OR with 1
    a = msat_make_bv_or(env, a, one32);
    b = msat_make_bv_or(env, b, one32);

    // Extract low 8 bits
    a = msat_make_bv_extract(env, 7, 0, a);
    b = msat_make_bv_extract(env, 7, 0, b);

    // Extend again to 32 bits
    a = msat_make_bv_zext(env, 24, a);
    b = msat_make_bv_zext(env, 24, b);

    // Shift left by 7
    a = msat_make_bv_lshl(env, a, seven32);
    b = msat_make_bv_lshl(env, b, seven32);

    // Extract low 8 bits again
    a = msat_make_bv_extract(env, 7, 0, a);
    b = msat_make_bv_extract(env, 7, 0, b);

    // Assert NOT (a == b)
    long eq = msat_make_equal(env, a, b);
    long neq = msat_make_not(env, eq);

    msat_assert_formula(env, neq);

    boolean isSat = msat_check_sat(env);
    assertThat(isSat).isFalse();

    long pm = msat_get_proof_manager(env);
    long proof = msat_get_proof(pm);

    msat_destroy_proof_manager(pm); // if this method is not there then there is no SIGSEV
  }

  private void testProofManager(long testEnv) throws SolverException, InterruptedException {
    const0 = msat_make_number(testEnv, "0");
    const1 = msat_make_number(testEnv, "1");
    long rationalType = msat_get_rational_type(testEnv);
    var = msat_make_variable(testEnv, "rat", rationalType);

    msat_push_backtrack_point(testEnv);

    msat_assert_formula(testEnv, msat_make_equal(testEnv, var, const0));
    msat_assert_formula(testEnv, msat_make_equal(testEnv, var, const1));

    // UNSAT
    assertThat(msat_check_sat(testEnv)).isFalse();

    long proofMgr = msat_get_proof_manager(testEnv);
    long proof = msat_get_proof(proofMgr);

    assertThat(msat_proof_is_term(proof)).isFalse();

    assertThat(msat_proof_get_arity(proof)).isEqualTo(1);

    String proofName = msat_proof_get_name(proof);
    assertThat(proofName).isEqualTo("res-chain");

    // Child is also a proof
    long proofChild = msat_proof_get_child(proof, 0);
    assertThat(msat_proof_get_name(proofChild)).isEqualTo("clause-hyp");
    assertThat(msat_proof_is_term(proofChild)).isFalse();
    assertThat(msat_proof_get_arity(proofChild)).isEqualTo(0);

    // Can be used to check for the equality of proofs
    int proofID = msat_proof_id(proof);
    int proofChildID = msat_proof_id(proofChild);
    assertThat(proofChildID).isNotEqualTo(proofID);

    // TODO: test term representation of a proof
    // long term = msat_proof_get_term(proofChild2);

    // Cleans up the proof manager and the associated proof
    msat_destroy_proof_manager(proofMgr);
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
  public void asinTest() throws SolverException, InterruptedException {
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

  // The next method crashed with MathSAT5 version 5.6.4
  // (NullPointer during iterator creation).
  // The bug was reported and fixed with the next release.
  @Test
  public void modelIteratorTest()
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

  private static final String LIA_QUERY =
      "(declare-fun |__ADDRESS_OF_main::a@| () Int)"
          + "(declare-fun |main::a@2| () Int)"
          + "(declare-fun *int@1 () (Array Int Int))"
          + "(declare-fun |main::p@2| () Int)"
          + "(declare-fun *int@2 () (Array Int Int))"
          + "(define-fun .8 () Int 0)"
          + "(define-fun .13 () Int |__ADDRESS_OF_main::a@|)"
          + "(define-fun .14 () Bool (<= .13 .8))"
          + "(define-fun .15 () Bool (not .14))"
          + "(define-fun .16 () Bool ((_ divisible 4) (- .13 .8)))"
          + "(define-fun .18 () Int (- 4))"
          + "(define-fun .19 () Bool (<= .13 .18))"
          + "(define-fun .20 () Bool (not .19))"
          + "(define-fun .21 () Int |main::a@2|)"
          + "(define-fun .22 () Bool (= .21 .8))"
          + "(define-fun .23 () Bool (and .15 .16))"
          + "(define-fun .24 () Bool (and .20 .23))"
          + "(define-fun .25 () Bool (and .22 .24))"
          + "(define-fun .26 () (Array Int Int) *int@1)"
          + "(define-fun .27 () Int (select .26 .13))"
          + "(define-fun .28 () Bool (= .21 .27))"
          + "(define-fun .29 () Int |main::p@2|)"
          + "(define-fun .30 () Bool (= .13 .29))"
          + "(define-fun .31 () Bool (and .28 .30))"
          + "(define-fun .32 () Bool (and .25 .31))"
          + "(define-fun .33 () Int 5)"
          + "(define-fun .34 () (Array Int Int) *int@2)"
          + "(define-fun .35 () (Array Int Int) (store .26 .13 .33))"
          + "(define-fun .36 () Bool (= .34 .35))"
          + "(define-fun .37 () Bool (and .32 .36))"
          + "(define-fun .38 () Int (select .34 .29))"
          + "(define-fun .39 () Bool (<= .38 .8))"
          + "(define-fun .40 () Bool (not .39))"
          + "(define-fun .43 () Bool (and .37 .40))"
          + "(assert .43)";

  @Test
  public void linearArithmeticModelTest()
      throws IllegalStateException, InterruptedException, SolverException {
    long parsed = msat_from_smtlib2(env, LIA_QUERY);
    msat_assert_formula(env, parsed);
    boolean isSat = msat_check_sat(env);
    assertThat(isSat).isTrue();

    long model = msat_get_model(env);
    long iter = msat_model_create_iterator(model);
    while (msat_model_iterator_has_next(iter)) {
      long[] key = new long[1];
      long[] value = new long[1];
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

  @Test
  public void evaluationWithoutModelTest()
      throws IllegalStateException, InterruptedException, SolverException {
    long x = msat_make_variable(env, "x", msat_get_integer_type(env));
    long num = msat_make_number(env, "10");

    msat_push_backtrack_point(env);
    msat_assert_formula(env, msat_make_equal(env, x, num));
    assertThat(msat_check_sat(env)).isTrue();

    boolean isSat = msat_check_sat(env);
    assertThat(isSat).isTrue();

    long value = msat_get_model_value(env, x);
    assertThat(msat_term_repr(value)).isEqualTo("10");
  }

  @Test
  public void enumTypeTest() throws SolverException, InterruptedException {
    String[] colors = {"blue", "red", "green"};

    // create enum type
    long colorType = msat_get_enum_type(env, "Color", 3, colors);
    assertThat(msat_type_repr(colorType)).isEqualTo("Color");

    // check type
    assertThat(msat_is_enum_type(env, colorType)).isTrue();
    assertThat(msat_is_enum_type(env, msat_get_integer_type(env))).isFalse();
    assertThat(msat_is_integer_type(env, colorType)).isFalse();

    // check constants
    long[] constantDecls = msat_get_enum_constants(env, colorType);
    assertThat(constantDecls.length).isEqualTo(3);
    for (int i = 0; i < colors.length; i++) {
      assertThat(msat_decl_get_name(constantDecls[i])).isEqualTo(colors[i]);
      assertThat(msat_decl_get_arity(constantDecls[i])).isEqualTo(0);
      assertThat(msat_term_get_type(msat_make_term(env, constantDecls[i], new long[] {})))
          .isEqualTo(colorType);
    }

    // check a simple assertion
    var = msat_make_variable(env, "varColor", colorType);
    long blue = msat_make_term(env, constantDecls[0], new long[] {});
    long red = msat_make_term(env, constantDecls[1], new long[] {});
    long green = msat_make_term(env, constantDecls[2], new long[] {});

    // check 1
    msat_push_backtrack_point(env);
    msat_assert_formula(env, msat_make_equal(env, blue, var));
    assertThat(msat_check_sat(env)).isTrue();
    msat_pop_backtrack_point(env);

    // chck 2
    msat_push_backtrack_point(env);
    msat_assert_formula(env, msat_make_not(env, msat_make_equal(env, blue, var)));
    assertThat(msat_check_sat(env)).isTrue();
    msat_assert_formula(env, msat_make_not(env, msat_make_equal(env, red, var)));
    assertThat(msat_check_sat(env)).isTrue();
    msat_assert_formula(env, msat_make_not(env, msat_make_equal(env, green, var)));
    assertThat(msat_check_sat(env)).isFalse();
    msat_pop_backtrack_point(env);
  }
}
