// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

import static com.google.common.truth.Truth.assertThat;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.util.Arrays;
import java.util.Locale;
import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorSolverContext.SatSolver;

public class BoolectorNativeApiTest {

  private long btor;

  @BeforeClass
  public static void load() {
    try {
      NativeLibraries.loadLibrary("boolector");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("Boolector is not available", e);
    }
  }

  @Before
  public void createEnvironment() {
    btor = BtorJNI.boolector_new();
  }

  @After
  public void freeEnvironment() {
    BtorJNI.boolector_delete(btor);
  }

  // some options have a different name in the API that their internal representation.
  // TODO why?
  // Because for some reason the return value of the get_opt method is not the correct option name
  // (check btortypes.h for correct options)
  private static final ImmutableMap<String, String> ALLOWED_DIFFS =
      ImmutableMap.<String, String>builder()
          .put("BTOR_OPT_ACKERMANNIZE", "BTOR_OPT_ACKERMANN")
          .put("BTOR_OPT_QUANT_DUAL", "BTOR_OPT_QUANT_DUAL_SOLVER")
          .put("BTOR_OPT_QUANT_SYNTHLIMIT", "BTOR_OPT_QUANT_SYNTH_LIMIT")
          .put("BTOR_OPT_QUANT_SYNTHQI", "BTOR_OPT_QUANT_SYNTH_QI")
          .put("BTOR_OPT_QUANT_MS", "BTOR_OPT_QUANT_MINISCOPE")
          .put("BTOR_OPT_QUANT_SYNTHCOMPLETE", "BTOR_OPT_QUANT_SYNTH_ITE_COMPLETE")
          .put("BTOR_OPT_BETA_REDUCE", "BTOR_OPT_BETA_REDUCE")
          .put("BTOR_OPT_DUMP_DIMACS", "BTOR_OPT_PRINT_DIMACS")
          .put("BTOR_OPT_SIMP_NORM_ADDS", "BTOR_OPT_SIMP_NORMAMLIZE_ADDERS")
          .buildOrThrow();

  @Test
  public void optionNameTest() {
    // check whether our enum is identical to Boolector's internal enum
    for (BtorOption option : BtorOption.values()) {
      String optName = BtorJNI.boolector_get_opt_lng(btor, option.getValue());
      String converted =
          "BTOR_OPT_"
              + optName.replace("-", "_").replace(":", "_").toUpperCase(Locale.getDefault());
      assertThat(option.name()).isEqualTo(ALLOWED_DIFFS.getOrDefault(converted, converted));
    }
  }

  @Test
  public void satSolverTest() {
    // check whether all sat solvers are available
    for (SatSolver satSolver : SatSolver.values()) {
      long btor1 = BtorJNI.boolector_new();
      BtorJNI.boolector_set_sat_solver(btor1, satSolver.name().toLowerCase(Locale.getDefault()));
      long newVar = BtorJNI.boolector_var(btor1, BtorJNI.boolector_bool_sort(btor1), "x");
      BtorJNI.boolector_assert(btor1, newVar);
      int result = BtorJNI.boolector_sat(btor1);
      assertThat(result).isEqualTo(BtorJNI.BTOR_RESULT_SAT_get());
      BtorJNI.boolector_delete(btor1);
    }
  }

  /**
   * For each available solver, we build a context and solver a small formula.
   *
   * <p>This should be sufficient to test whether the sat-solver can be loaded.
   */
  @Test
  public void satSolverBackendTest()
      throws InvalidConfigurationException, InterruptedException, SolverException {

    for (SatSolver satsolver : BoolectorSolverContext.SatSolver.values()) {
      ConfigurationBuilder config =
          Configuration.builder().setOption("solver.boolector.satSolver", satsolver.name());
      try (BoolectorSolverContext context =
          BoolectorSolverContext.create(
              config.build(),
              ShutdownNotifier.createDummy(),
              null,
              1,
              NativeLibraries::loadLibrary,
              LogManager.createTestLogManager())) {
        BooleanFormulaManager bfmgr = context.getFormulaManager().getBooleanFormulaManager();
        BooleanFormula fa = bfmgr.makeVariable("a");
        BooleanFormula fb = bfmgr.makeVariable("b");
        BooleanFormula fc = bfmgr.makeVariable("c");
        BooleanFormula f1 = bfmgr.or(fa, fb, fc);
        BooleanFormula f2 = bfmgr.and(fa, fb, fc);
        try (ProverEnvironment prover = context.newProverEnvironment()) {
          prover.addConstraint(bfmgr.equivalence(f1, f2));
          assertThat(prover.isUnsat()).isFalse();
        }
      }
    }
  }

  @Test
  public void dumpVariableTest() throws InvalidConfigurationException {
    ConfigurationBuilder config = Configuration.builder();
    try (BoolectorSolverContext context =
        BoolectorSolverContext.create(
            config.build(),
            ShutdownNotifier.createDummy(),
            null,
            1,
            NativeLibraries::loadLibrary,
            LogManager.createTestLogManager())) {
      FormulaManager mgr = context.getFormulaManager();
      BooleanFormulaManager bfmgr = mgr.getBooleanFormulaManager();
      for (String name : ImmutableList.of("a", "a", "b", "abc", "ABC")) {
        BooleanFormula f = bfmgr.makeVariable(name);
        String s = mgr.dumpFormula(f).toString();
        assertThat(s).contains(String.format("(declare-fun %s () (_ BitVec 1))", name));
        // assertThat(s).contains(String.format("(assert %s)", name)); // assertion not available
      }
    }
  }

  @Test
  public void dumpVariableWithAssertionsOnStackTest()
      throws InvalidConfigurationException, InterruptedException {
    ConfigurationBuilder config = Configuration.builder();
    try (BoolectorSolverContext context =
        BoolectorSolverContext.create(
            config.build(),
            ShutdownNotifier.createDummy(),
            null,
            1,
            NativeLibraries::loadLibrary,
            LogManager.createTestLogManager())) {
      FormulaManager mgr = context.getFormulaManager();
      BooleanFormulaManager bfmgr = mgr.getBooleanFormulaManager();
      try (ProverEnvironment prover = context.newProverEnvironment()) {
        prover.push(bfmgr.makeVariable("x"));
        for (String name : ImmutableList.of("a", "a", "b", "abc", "ABC")) {
          BooleanFormula f = bfmgr.makeVariable(name);
          String s = mgr.dumpFormula(f).toString();
          // TODO why is there a prefix "BTOR_2@"?
          // Possible reason: we are on the second level of the solver stack.
          // - first level comes from the constructor of ReusableStackTheoremProver.
          // - second level comes from the PUSH above.
          // We do actually not want to have such names in the dump.
          assertThat(s).contains(String.format("(declare-fun BTOR_2@%s () (_ BitVec 1))", name));
          // assertThat(s).contains(String.format("(assert "));
        }
      }
    }
  }

  @Test
  public void repeatedDumpFormulaTest() throws InvalidConfigurationException {
    ConfigurationBuilder config = Configuration.builder();
    try (BoolectorSolverContext context =
        BoolectorSolverContext.create(
            config.build(),
            ShutdownNotifier.createDummy(),
            null,
            1,
            NativeLibraries::loadLibrary,
            LogManager.createTestLogManager())) {
      FormulaManager mgr = context.getFormulaManager();
      BooleanFormulaManager bfmgr = mgr.getBooleanFormulaManager();
      BooleanFormula fa = bfmgr.makeVariable("a");
      BooleanFormula fb = bfmgr.makeVariable("b");
      BooleanFormula fc = bfmgr.makeVariable("c");
      BooleanFormula f1 = bfmgr.or(fa, bfmgr.and(fb, fc));
      BooleanFormula f2 = bfmgr.or(fa, bfmgr.and(fb, fc));
      String s1 = mgr.dumpFormula(f1).toString();
      // repeat several times to increase probability for non-deterministic behavior
      for (int i = 0; i < 10; i++) {
        assertThat(s1).isEqualTo(mgr.dumpFormula(f2).toString());
      }
    }
  }

  /*
   * Test Boolector model with bvs
   * x > 0 && y > 0 && x <= 100 && y <= 100 && x * y < 100 with overflow protection
   */
  @Test
  public void bvModelTest() {
    // Activate model gen
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_MODEL_GEN.getValue(), 1);

    // Create the formula and assert
    long bvSort = BtorJNI.boolector_bitvec_sort(btor, 8);

    long x = BtorJNI.boolector_var(btor, bvSort, "x");
    long y = BtorJNI.boolector_var(btor, bvSort, "y");
    long zero = BtorJNI.boolector_zero(btor, bvSort);
    long hundred = BtorJNI.boolector_int(btor, 100, bvSort);

    long zeroLTX = BtorJNI.boolector_ult(btor, zero, x);
    long xLTEHundred = BtorJNI.boolector_ulte(btor, x, hundred);
    long zeroLTY = BtorJNI.boolector_ult(btor, zero, y);
    long yLTEHundred = BtorJNI.boolector_ulte(btor, y, hundred);
    long mulXY = BtorJNI.boolector_mul(btor, y, x);
    long mulXYLTHundred = BtorJNI.boolector_ult(btor, mulXY, hundred);

    long formulaBigger0 = BtorJNI.boolector_and(btor, zeroLTX, zeroLTY);
    long formulaLTE100 = BtorJNI.boolector_and(btor, xLTEHundred, yLTEHundred);
    long formula0And100 = BtorJNI.boolector_and(btor, formulaBigger0, formulaLTE100);
    long formula = BtorJNI.boolector_and(btor, mulXYLTHundred, formula0And100);
    BtorJNI.boolector_assert(btor, formula);
    // Overflow protection
    long overflow = BtorJNI.boolector_not(btor, BtorJNI.boolector_umulo(btor, x, y));
    BtorJNI.boolector_assert(btor, overflow);
    // Check SAT
    assertThat(BtorJNI.boolector_sat(btor)).isEqualTo(BtorJNI.BTOR_RESULT_SAT_get());

    // use get_value() to get values from nodes
    long xValue = BtorJNI.boolector_get_value(btor, x);
    long yValue = BtorJNI.boolector_get_value(btor, y);

    // check the type
    assertThat(BtorJNI.boolector_get_sort(btor, xValue))
        .isEqualTo(BtorJNI.boolector_get_sort(btor, x));
    assertThat(BtorJNI.boolector_get_sort(btor, yValue))
        .isEqualTo(BtorJNI.boolector_get_sort(btor, y));

    String xValueString = BtorJNI.boolector_bv_assignment(btor, xValue);
    String yValueString = BtorJNI.boolector_bv_assignment(btor, yValue);

    // Check that the values are the same
    assertThat(xValueString).isEqualTo(BtorJNI.boolector_bv_assignment(btor, x));
    assertThat(yValueString).isEqualTo(BtorJNI.boolector_bv_assignment(btor, y));
    assertThat(Integer.parseInt(xValueString, 2) * Integer.parseInt(yValueString, 2))
        .isLessThan(100);
    assertThat(Integer.parseInt(xValueString, 2)).isAtMost(100);
    assertThat(Integer.parseInt(yValueString, 2)).isAtMost(100);
    assertThat(Integer.parseInt(xValueString, 2)).isAtLeast(1);
    assertThat(Integer.parseInt(yValueString, 2)).isAtLeast(1);
  }

  /*
   * Test array model for Boolector.
   *    (= (select arr 5) x)
   *    (= x 123)
   *    (= (select arr 2) y)
   *    (= y 0)
   */
  @Test
  public void bvArrayModelTest() {
    // Activate model gen
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_MODEL_GEN.getValue(), 1);

    // Create the formula and assert
    long bvSort = BtorJNI.boolector_bitvec_sort(btor, 8);
    long arraySort = BtorJNI.boolector_array_sort(btor, bvSort, bvSort);

    long array = BtorJNI.boolector_array(btor, arraySort, "array");
    long x = BtorJNI.boolector_var(btor, bvSort, "x");
    long y = BtorJNI.boolector_var(btor, bvSort, "y");
    long zero = BtorJNI.boolector_zero(btor, bvSort);
    long const123 = BtorJNI.boolector_int(btor, 123, bvSort);
    long const2 = BtorJNI.boolector_int(btor, 2, bvSort);
    long const5 = BtorJNI.boolector_int(btor, 5, bvSort);
    // (= (select arr 5) x)
    long xEqArrayAt5 = BtorJNI.boolector_eq(btor, x, BtorJNI.boolector_read(btor, array, const5));
    // (= x 123)
    long xEq123 = BtorJNI.boolector_eq(btor, x, const123);
    // (= y 0)
    long yEq0 = BtorJNI.boolector_eq(btor, y, zero);
    // (= (select arr 2) y)
    long yEqArrayAt2 = BtorJNI.boolector_eq(btor, y, BtorJNI.boolector_read(btor, array, const2));

    long arrayAt5Formulas = BtorJNI.boolector_and(btor, xEqArrayAt5, xEq123);
    long arrayAt2Formulas = BtorJNI.boolector_and(btor, yEq0, yEqArrayAt2);
    long formula = BtorJNI.boolector_and(btor, arrayAt5Formulas, arrayAt2Formulas);
    BtorJNI.boolector_assert(btor, formula);

    // Check SAT
    assertThat(BtorJNI.boolector_sat(btor)).isEqualTo(BtorJNI.BTOR_RESULT_SAT_get());

    // use get_value() to get values from nodes
    long xValue = BtorJNI.boolector_get_value(btor, x);
    long yValue = BtorJNI.boolector_get_value(btor, y);
    long arrayValue = BtorJNI.boolector_get_value(btor, array);

    // check the type
    assertThat(BtorJNI.boolector_get_sort(btor, xValue))
        .isEqualTo(BtorJNI.boolector_get_sort(btor, x));
    assertThat(BtorJNI.boolector_get_sort(btor, yValue))
        .isEqualTo(BtorJNI.boolector_get_sort(btor, y));
    assertThat(BtorJNI.boolector_get_sort(btor, arrayValue))
        .isEqualTo(BtorJNI.boolector_get_sort(btor, array));

    // Check that the values are the same
    assertThat(BtorJNI.boolector_bv_assignment(btor, xValue))
        .isEqualTo(BtorJNI.boolector_bv_assignment(btor, x));
    assertThat(BtorJNI.boolector_bv_assignment(btor, yValue))
        .isEqualTo(BtorJNI.boolector_bv_assignment(btor, y));
    // The assignment_helper generates the assignments in a array of arrays!
    String[][] arrayValueHelperArray = BtorJNI.boolector_array_assignment_helper(btor, arrayValue);
    String[] arrayValueIndices = arrayValueHelperArray[0];
    Arrays.sort(arrayValueIndices);
    String[] arrayValueValues = arrayValueHelperArray[1];
    Arrays.sort(arrayValueValues);
    String[][] arrayHelperArray = BtorJNI.boolector_array_assignment_helper(btor, array);
    String[] arrayIndices = arrayHelperArray[0];
    Arrays.sort(arrayIndices);
    String[] arrayValues = arrayHelperArray[1];
    Arrays.sort(arrayValues);

    // TODO: Is it better to convert arrays into lists and check via containsExactlyElementsIn() or
    // sort them and compare?
    assertThat(arrayValueIndices).isEqualTo(arrayIndices);
    assertThat(arrayValueValues).isEqualTo(arrayValues);
    assertThat(arrayValueIndices).asList().containsExactly("00000010", "00000101");
    assertThat(arrayValueValues).asList().containsExactly("00000000", "01111011");
  }

  /*
   * Test uf model for Boolector.
   *    (= f(x) 5)
   *    (= x 123)
   *    (= g(2) y)
   *    (= y 0)
   */
  @Test
  public void ufModelTest1() {
    // Activate model gen
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_MODEL_GEN.getValue(), 1);

    // Create the formula and assert
    long bvSort = BtorJNI.boolector_bitvec_sort(btor, 8);
    long funSort = BtorJNI.boolector_fun_sort(btor, new long[] {bvSort}, 1, bvSort);

    long uf1 = BtorJNI.boolector_uf(btor, funSort, "f");
    long uf2 = BtorJNI.boolector_uf(btor, funSort, "g");

    long x = BtorJNI.boolector_var(btor, bvSort, "x");
    long y = BtorJNI.boolector_var(btor, bvSort, "y");
    long zero = BtorJNI.boolector_zero(btor, bvSort);
    long const123 = BtorJNI.boolector_int(btor, 123, bvSort);
    long const2 = BtorJNI.boolector_int(btor, 2, bvSort);
    long const5 = BtorJNI.boolector_int(btor, 5, bvSort);

    long applyUf1EqX =
        BtorJNI.boolector_eq(btor, BtorJNI.boolector_apply(btor, new long[] {x}, 1, uf1), const5);
    long xEq123 = BtorJNI.boolector_eq(btor, x, const123);
    long yEq0 = BtorJNI.boolector_eq(btor, y, zero);
    long applyUf2EqY =
        BtorJNI.boolector_eq(btor, BtorJNI.boolector_apply(btor, new long[] {const2}, 1, uf2), y);

    long subformula1 = BtorJNI.boolector_and(btor, applyUf1EqX, xEq123);
    long subformula2 = BtorJNI.boolector_and(btor, yEq0, applyUf2EqY);
    long formula = BtorJNI.boolector_and(btor, subformula1, subformula2);
    BtorJNI.boolector_assert(btor, formula);

    // Check SAT
    assertThat(BtorJNI.boolector_sat(btor)).isEqualTo(BtorJNI.BTOR_RESULT_SAT_get());

    // use get_value() to get values from nodes
    long xValue = BtorJNI.boolector_get_value(btor, x);
    long yValue = BtorJNI.boolector_get_value(btor, y);
    long uf1Value = BtorJNI.boolector_get_value(btor, uf1);
    long uf2Value = BtorJNI.boolector_get_value(btor, uf2);

    // check the type
    assertThat(BtorJNI.boolector_get_sort(btor, uf1Value))
        .isEqualTo(BtorJNI.boolector_get_sort(btor, uf1));
    assertThat(BtorJNI.boolector_get_sort(btor, uf2Value))
        .isEqualTo(BtorJNI.boolector_get_sort(btor, uf2));

    String[][] uf1Assignments = BtorJNI.boolector_uf_assignment_helper(btor, uf1);
    String[][] uf2Assignments = BtorJNI.boolector_uf_assignment_helper(btor, uf2);

    // Check that the values are the same
    assertThat(BtorJNI.boolector_bv_assignment(btor, xValue))
        .isEqualTo(BtorJNI.boolector_bv_assignment(btor, x));
    assertThat(BtorJNI.boolector_bv_assignment(btor, yValue))
        .isEqualTo(BtorJNI.boolector_bv_assignment(btor, y));

    // Argument of f (=123)
    assertThat(uf1Assignments[0][0]).isEqualTo("01111011");
    // Value of f (=5)
    assertThat(uf1Assignments[1][0]).isEqualTo("00000101");
    // Argument of g (=2)
    assertThat(uf2Assignments[0][0]).isEqualTo("00000010");
    // Value of g (=0)
    assertThat(uf2Assignments[1][0]).isEqualTo("00000000");
  }

  /*
   * Test that the value node stays valid if the values from which it is derived change.
   *
   * x > 0 && y > 0 && x <= 100 && y <= 100 && x * y < 100 with overflow protection
   * Get value nodes. Check value for x and y and add inequalities such that they can't
   * be the same value as before. Check SAT and get new value nodes and check all
   * value nodes.
   */
  @Test
  public void bvModelConsistencyTest() {
    // Activate model gen
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_MODEL_GEN.getValue(), 1);
    // Incremental mode to enable multiple SAT calls
    BtorJNI.boolector_set_opt(btor, BtorOption.BTOR_OPT_INCREMENTAL.getValue(), 1);

    // Create the formula and assert
    long bvSort = BtorJNI.boolector_bitvec_sort(btor, 8);

    long x = BtorJNI.boolector_var(btor, bvSort, "x");
    long y = BtorJNI.boolector_var(btor, bvSort, "y");
    long zero = BtorJNI.boolector_zero(btor, bvSort);
    long hundred = BtorJNI.boolector_int(btor, 100, bvSort);

    long zeroLTX = BtorJNI.boolector_ult(btor, zero, x);
    long xLTEHundred = BtorJNI.boolector_ulte(btor, x, hundred);
    long zeroLTY = BtorJNI.boolector_ult(btor, zero, y);
    long yLTEHundred = BtorJNI.boolector_ulte(btor, y, hundred);
    long mulXY = BtorJNI.boolector_mul(btor, y, x);
    long mulXYLTHundred = BtorJNI.boolector_ult(btor, mulXY, hundred);

    long formulaBigger0 = BtorJNI.boolector_and(btor, zeroLTX, zeroLTY);
    long formulaLTE100 = BtorJNI.boolector_and(btor, xLTEHundred, yLTEHundred);
    long formula0And100 = BtorJNI.boolector_and(btor, formulaBigger0, formulaLTE100);
    long formula = BtorJNI.boolector_and(btor, mulXYLTHundred, formula0And100);
    BtorJNI.boolector_assert(btor, formula);
    // Overflow protection
    long overflow = BtorJNI.boolector_not(btor, BtorJNI.boolector_umulo(btor, x, y));
    BtorJNI.boolector_assert(btor, overflow);
    // Check SAT
    assertThat(BtorJNI.boolector_sat(btor)).isEqualTo(BtorJNI.BTOR_RESULT_SAT_get());

    // remember values and nodes
    long xValueInitial = BtorJNI.boolector_get_value(btor, x);
    long yValueInitial = BtorJNI.boolector_get_value(btor, y);
    String xStringInitial = BtorJNI.boolector_bv_assignment(btor, xValueInitial);
    String yStringInitial = BtorJNI.boolector_bv_assignment(btor, yValueInitial);

    // Add x != old value and the same for y
    long xNEQx =
        BtorJNI.boolector_not(
            btor,
            BtorJNI.boolector_eq(
                btor, BtorJNI.boolector_int(btor, Integer.parseInt(xStringInitial, 2), bvSort), x));
    long yNEQy =
        BtorJNI.boolector_not(
            btor,
            BtorJNI.boolector_eq(
                btor, BtorJNI.boolector_int(btor, Integer.parseInt(yStringInitial, 2), bvSort), y));
    long formulaVarsNE = BtorJNI.boolector_and(btor, xNEQx, yNEQy);
    BtorJNI.boolector_assert(btor, formulaVarsNE);
    // Check SAT again
    assertThat(BtorJNI.boolector_sat(btor)).isEqualTo(BtorJNI.BTOR_RESULT_SAT_get());

    long xValueNew = BtorJNI.boolector_get_value(btor, x);
    long yValueNew = BtorJNI.boolector_get_value(btor, y);
    String xStringNew = BtorJNI.boolector_bv_assignment(btor, xValueNew);
    String yStringNew = BtorJNI.boolector_bv_assignment(btor, yValueNew);

    // Check that the values are not the same
    assertThat(xStringInitial).isNotEqualTo(xStringNew);
    assertThat(yStringInitial).isNotEqualTo(yStringNew);
  }
}
