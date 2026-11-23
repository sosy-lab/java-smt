// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.yices2;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assertWithMessage;
import static org.junit.Assert.assertThrows;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.sri.yices.Model;
import com.sri.yices.Status;
import com.sri.yices.Yices;
import com.sri.yices.YicesException;
import java.math.BigInteger;
import java.util.Random;
import org.junit.Test;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.yices2.Yices2SolverContext.Yices2Parameters;
import org.sosy_lab.java_smt.test.SolverBasedTest0;

public class Yices2NativeOptionsTest extends SolverBasedTest0 {

  private static final ImmutableList<String> SOLVER_TYPES = ImmutableList.of("dpllt", "mcsat");
  private static final ImmutableList<String> MODES =
      ImmutableList.of("one-shot", "multi-checks", "push-pop", "interactive");
  private static final ImmutableList<String> LINEAR_LOGICS = ImmutableList.of("ALL", "QF_LIA");
  private static final ImmutableList<String> NON_LINEAR_LOGICS =
      ImmutableList.of("QF_NIA", "QF_AUFNIRA");

  // Yices error code CTX_OPERATION_NOT_SUPPORTED
  private static final int OPERATION_NOT_SUPPORTED = 401;

  @Override
  protected Solvers solverToUse() {
    return Solvers.YICES2;
  }

  /** Yices uses MCSAT for non-linear arithmetic and finite fields (see logic2arch in Yices). */
  private static boolean expectMcsat(String logic) {
    return logic.contains("NIA")
        || logic.contains("NRA")
        || logic.contains("NIRA")
        || logic.equals("QF_FFA");
  }

  private static boolean expectPushSupport(String mode) {
    return mode.equals("push-pop") || mode.equals("interactive");
  }

  /**
   * Checks which engine a new prover uses. Yices only supports a check with a model in MCSAT, and
   * reports an error for DPLL(T). On MCSAT this runs a check, so the prover is not reused.
   */
  private boolean usesMcsat() {
    try (Yices2AbstractProver<?> prover =
            (Yices2AbstractProver<?>)
                ((Yices2SolverContext) context).newProverEnvironment0(ImmutableSet.of());
        Model model = new Model()) {
      Status status = prover.curEnv.checkWithModel(null, model, new int[0]);
      if (status == Status.ERROR) {
        assertThat(Yices.errorCode()).isEqualTo(OPERATION_NOT_SUPPORTED);
        return false;
      }
      assertThat(status).isEqualTo(Status.SAT);
      return true;
    }
  }

  private boolean supportsPush() throws InterruptedException {
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.push();
      return true;
    } catch (YicesException e) {
      assertThat(e).hasMessageThat().contains("operation not supported by the context");
      return false;
    }
  }

  /** Creates x * y = 6. */
  private BooleanFormula makeNonLinearFormula() {
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    return imgr.equal(imgr.multiply(x, y), imgr.makeNumber(6));
  }

  /** x / 0 = 3, which is satisfiable as SMT-LIB leaves division by zero unspecified. */
  private BooleanFormula makeDivisionByZeroFormula() {
    IntegerFormula x = imgr.makeVariable("x");
    return imgr.equal(imgr.divide(x, imgr.makeNumber(0)), imgr.makeNumber(3));
  }

  /** Creates a = store(const(0), 1, 2), which needs a constant array. */
  private BooleanFormula makeConstantArrayFormula() {
    ArrayFormula<IntegerFormula, IntegerFormula> zeros =
        amgr.makeArray(FormulaType.IntegerType, FormulaType.IntegerType, imgr.makeNumber(0));
    ArrayFormula<IntegerFormula, IntegerFormula> a =
        amgr.makeArray("a", FormulaType.IntegerType, FormulaType.IntegerType);
    return amgr.equivalence(a, amgr.store(zeros, imgr.makeNumber(1), imgr.makeNumber(2)));
  }

  /** Creates x * y = 1040399 = 1019 * 1021 with 1 < x, y < 2^16 as 32-bit bitvectors. */
  private BooleanFormula makeFactoringFormula(BitvectorFormula x, BitvectorFormula y) {
    BitvectorFormula one = bvmgr.makeBitvector(32, 1);
    BitvectorFormula limit = bvmgr.makeBitvector(32, 1 << 16);
    return bmgr.and(
        bvmgr.equal(bvmgr.multiply(x, y), bvmgr.makeBitvector(32, 1040399)),
        bvmgr.greaterThan(x, one, false),
        bvmgr.greaterThan(y, one, false),
        bvmgr.lessThan(x, limit, false),
        bvmgr.lessThan(y, limit, false));
  }

  /**
   * Creates a job shop scheduling problem with random durations, where every job runs on all
   * machines in order, a machine runs one job at a time, and all jobs finish before the deadline.
   * This only needs difference logic.
   */
  private BooleanFormula makeJobShopFormula(int jobs, int machines, int deadline) {
    Random random = new Random(3);
    ImmutableList.Builder<BooleanFormula> constraints = ImmutableList.builder();
    IntegerFormula[][] start = new IntegerFormula[jobs][machines];
    int[][] duration = new int[jobs][machines];
    for (int j = 0; j < jobs; j++) {
      for (int m = 0; m < machines; m++) {
        start[j][m] = imgr.makeVariable("start_" + j + "_" + m);
        duration[j][m] = 1 + random.nextInt(9);
        constraints.add(imgr.greaterOrEquals(start[j][m], imgr.makeNumber(0)));
        constraints.add(imgr.lessOrEquals(start[j][m], imgr.makeNumber(deadline - duration[j][m])));
        if (m > 0) {
          constraints.add(isBefore(start[j][m - 1], duration[j][m - 1], start[j][m]));
        }
      }
    }
    for (int m = 0; m < machines; m++) {
      for (int i = 0; i < jobs; i++) {
        for (int j = i + 1; j < jobs; j++) {
          constraints.add(
              bmgr.or(
                  isBefore(start[i][m], duration[i][m], start[j][m]),
                  isBefore(start[j][m], duration[j][m], start[i][m])));
        }
      }
    }
    return bmgr.and(constraints.build());
  }

  /** Creates start1 + duration1 <= start2 as start1 - start2 <= -duration1. */
  private BooleanFormula isBefore(IntegerFormula start1, int duration1, IntegerFormula start2) {
    return imgr.lessOrEquals(imgr.subtract(start1, start2), imgr.makeNumber(-duration1));
  }

  /** Requests a shutdown after the given time, so that a slow check is interrupted. */
  private void shutdownAfter(long millis) {
    Thread thread =
        new Thread(
            () -> {
              try {
                Thread.sleep(millis);
                shutdownManager.requestShutdown("Timeout");
              } catch (InterruptedException e) {
                throw new UnsupportedOperationException("Unexpected interrupt", e);
              }
            });
    thread.setDaemon(true);
    thread.start();
  }

  private void assertNonLinearArithmeticIsSupported(String message)
      throws SolverException, InterruptedException {
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.push(makeNonLinearFormula());
      assertWithMessage(message).that(prover.isUnsat()).isFalse();
      prover.pop();
      prover.push(makeDivisionByZeroFormula());
      assertWithMessage(message).that(prover.isUnsat()).isFalse();
    }
  }

  private void assertNonLinearArithmeticIsRejected(String message) {
    BooleanFormula nonLinear = makeNonLinearFormula();
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      YicesException e = assertThrows(YicesException.class, () -> prover.addConstraint(nonLinear));
      assertWithMessage(message).that(e).hasMessageThat().contains("non-linear arithmetic");
    }
    BooleanFormula divisionByZero = makeDivisionByZeroFormula();
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      YicesException e =
          assertThrows(YicesException.class, () -> prover.addConstraint(divisionByZero));
      assertWithMessage(message).that(e).hasMessageThat().contains("division by zero");
    }
  }

  @Test
  public void defaultUsesMcsatTest() throws SolverException, InterruptedException {
    assertThat(usesMcsat()).isTrue();
    assertNonLinearArithmeticIsSupported("default");
    assertThat(supportsPush()).isTrue();
  }

  @Test
  public void solverTypeSelectsEngineTest() throws InvalidConfigurationException {
    for (String solverType : SOLVER_TYPES) {
      setAdditionalConfigOptionForSolver("solver.yices2.solverType", solverType);
      assertWithMessage("MCSAT is used for solver type %s", solverType)
          .that(usesMcsat())
          .isEqualTo(solverType.equals("mcsat"));
    }
  }

  @Test
  public void logicOverridesSolverTypeTest()
      throws ReflectiveOperationException, InvalidConfigurationException {
    Option logicOption =
        Yices2Parameters.class.getDeclaredField("logic").getAnnotation(Option.class);
    for (String logic : logicOption.values()) {
      for (String solverType : SOLVER_TYPES) {
        setAdditionalConfigOptionForSolver(
            "solver.yices2.logic", logic, "solver.yices2.solverType", solverType);
        assertWithMessage("MCSAT is used for logic %s and solver type %s", logic, solverType)
            .that(usesMcsat())
            .isEqualTo(expectMcsat(logic));
      }
    }
  }

  @Test
  public void nonLinearArithmeticWithMcsatTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    setAdditionalConfigOptionForSolver("solver.yices2.solverType", "mcsat");
    assertNonLinearArithmeticIsSupported("solver type mcsat");
    for (String logic : NON_LINEAR_LOGICS) {
      // The logic selects MCSAT, although the solver type is DPLL(T)
      setAdditionalConfigOptionForSolver(
          "solver.yices2.logic", logic, "solver.yices2.solverType", "dpllt");
      assertNonLinearArithmeticIsSupported(logic);
    }
  }

  @Test
  public void nonLinearArithmeticWithDplltTest() throws InvalidConfigurationException {
    setAdditionalConfigOptionForSolver("solver.yices2.solverType", "dpllt");
    assertNonLinearArithmeticIsRejected("solver type dpllt");
    for (String logic : LINEAR_LOGICS) {
      // The logic selects DPLL(T), although the solver type is MCSAT
      setAdditionalConfigOptionForSolver(
          "solver.yices2.logic", logic, "solver.yices2.solverType", "mcsat");
      assertNonLinearArithmeticIsRejected(logic);
    }
  }

  @Test
  public void constantArraysTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    setAdditionalConfigOptionForSolver("solver.yices2.solverType", "dpllt");
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.push(makeConstantArrayFormula());
      assertThat(prover.isUnsat()).isFalse();
    }

    // MCSAT does not support constant arrays
    setAdditionalConfigOptionForSolver("solver.yices2.solverType", "mcsat");
    BooleanFormula constantArray = makeConstantArrayFormula();
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      YicesException e =
          assertThrows(YicesException.class, () -> prover.addConstraint(constantArray));
      assertThat(e).hasMessageThat().contains("lambda terms");
    }
  }

  @Test
  public void factoringWithMcsatTimeoutTest() throws SolverException, InterruptedException {
    // MCSAT does not finish this within 10s, see factoringWithBitvectorLogicTest()
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.push(makeFactoringFormula(bvmgr.makeVariable(32, "x"), bvmgr.makeVariable(32, "y")));
      shutdownAfter(1000);
      assertThrows(InterruptedException.class, prover::isUnsat);
    }
  }

  @Test
  public void factoringWithBitvectorLogicTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    // The logic QF_BV selects DPLL(T) with bit-blasting, which solves this in ~30ms
    setAdditionalConfigOptionForSolver("solver.yices2.logic", "QF_BV");
    BitvectorFormula x = bvmgr.makeVariable(32, "x");
    BitvectorFormula y = bvmgr.makeVariable(32, "y");
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(makeFactoringFormula(x, y));
      shutdownAfter(10_000);
      assertThat(prover.isUnsat()).isFalse();
      try (var model = prover.getModel()) {
        assertThat(ImmutableSet.of(model.evaluate(x), model.evaluate(y)))
            .containsExactly(BigInteger.valueOf(1019), BigInteger.valueOf(1021));
      }
    }
  }

  @Test
  public void jobShopWithDifferenceLogicTest()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    // With the logic QF_IDL and the mode 'one-shot', Yices can use its Floyd-Warshall solver.
    // This solves both checks in ~10ms, while the default MCSAT needs ~1s and ~4s,
    // and DPLL(T) without a logic ~0.9s and ~0.1s.
    setAdditionalConfigOptionForSolver(
        "solver.yices2.logic", "QF_IDL", "solver.yices2.mode", "one-shot");
    shutdownAfter(10_000);
    // The mode 'one-shot' only allows a single check, so we use a new prover for each check
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.addConstraint(makeJobShopFormula(10, 5, 64));
      assertThat(prover.isUnsat()).isTrue();
    }
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      prover.addConstraint(makeJobShopFormula(10, 5, 80));
      assertThat(prover.isUnsat()).isFalse();
    }
  }

  @Test
  public void mcsatWithoutLogicOnlySupportsPushPopTest() {
    for (String mode : MODES) {
      if (mode.equals("push-pop")) {
        continue;
      }
      InvalidConfigurationException e =
          assertThrows(
              InvalidConfigurationException.class,
              () -> setAdditionalConfigOptionForSolver("solver.yices2.mode", mode));
      assertThat(e).hasMessageThat().contains("only supports the mode 'push-pop'");
    }
  }

  @Test
  public void modeWithDplltTest() throws InvalidConfigurationException, InterruptedException {
    for (String mode : MODES) {
      setAdditionalConfigOptionForSolver(
          "solver.yices2.solverType", "dpllt", "solver.yices2.mode", mode);
      assertWithMessage("push is supported in mode %s", mode)
          .that(supportsPush())
          .isEqualTo(expectPushSupport(mode));
    }
  }

  @Test
  public void modeWithLogicTest() throws InvalidConfigurationException, InterruptedException {
    // With a logic, all modes are supported for both DPLL(T) and MCSAT
    for (String logic : ImmutableList.of("QF_LIA", "QF_NIA")) {
      for (String mode : MODES) {
        setAdditionalConfigOptionForSolver(
            "solver.yices2.logic", logic, "solver.yices2.mode", mode);
        assertWithMessage("push is supported for logic %s in mode %s", logic, mode)
            .that(supportsPush())
            .isEqualTo(expectPushSupport(mode));
      }
    }
  }
}
