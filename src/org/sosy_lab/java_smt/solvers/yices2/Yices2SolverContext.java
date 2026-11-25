// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import com.sri.yices.Yices;
import java.util.Set;
import java.util.function.Consumer;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public final class Yices2SolverContext extends AbstractSolverContext {

  @Options(prefix = "solver.yices2")
  static class Yices2Parameters {
    @Option(
        secure = true,
        description =
            "Backend to use for the solver: MCSAT supports non-linear arithmetic and division by"
                + " zero, DPLL(T) supports constant arrays. This option is ignored if a logic is"
                + " set with solver.yices2.logic, as the logic then determines the backend."
                + " Without a logic, MCSAT only supports the mode 'push-pop'.",
        values = {"dpllt", "mcsat"})
    String solverType = "mcsat";

    @Option(
        secure = true,
        description =
            "Sets the SMTLIB logic for solver selection. If a logic is set, it determines the"
                + " backend and solver.yices2.solverType is ignored: non-linear logics like"
                + " QF_NIA or QF_AUFNIRA and the logic QF_FFA use MCSAT, all other logics use"
                + " DPLL(T). Setting the logic to ALL will select DPLL(T) with all theories"
                + " enabled, and NONE means that only boolean logic is supported. If the selected"
                + " logic is QF_IDL or QF_RDL and the mode is set to 'one-shot', Yices may either"
                + " use its Floyd-Warshall solver, or the more general Simplex solver, based on an"
                + " internal heuristic.",
        values = {
          "ALL",
          "NONE",
          "QF_ABV",
          "QF_ALIA",
          "QF_ALIRA",
          "QF_ALRA",
          "QF_ANIA",
          "QF_ANIRA",
          "QF_ANRA",
          "QF_AUF",
          "QF_AUFBV",
          "QF_AUFBVLIA",
          "QF_AUFBVNIA",
          "QF_AUFLIA",
          "QF_AUFLIRA",
          "QF_AUFLRA",
          "QF_AUFNIA",
          "QF_AUFNIRA",
          "QF_AUFNRA",
          "QF_AX",
          "QF_BV",
          "QF_BVLRA",
          "QF_FFA",
          "QF_IDL",
          "QF_LIA",
          "QF_LIRA",
          "QF_LRA",
          "QF_NIA",
          "QF_NIRA",
          "QF_NRA",
          "QF_RDL",
          "QF_UF",
          "QF_UFBV",
          "QF_UFBVLIA",
          "QF_UFIDL",
          "QF_UFLIA",
          "QF_UFLIRA",
          "QF_UFLRA",
          "QF_UFNIA",
          "QF_UFNIRA",
          "QF_UFNRA",
          "QF_UFRDL"
        })
    @Nullable String logic;

    @Option(
        secure = true,
        description =
            "Configures the solver to allow/disable multiple SAT checks: 'one-shot' allows only"
                + " a single check, 'multi-checks' allows several checks but no push/pop,"
                + " 'push-pop' allows push/pop, and 'interactive' additionally allows to continue"
                + " after an interrupted check. Push/pop, assumptions and unsat cores need"
                + " 'push-pop' or 'interactive'. If solver.yices2.solverType is 'mcsat' and no"
                + " logic is set, only 'push-pop' is supported.",
        values = {"one-shot", "multi-checks", "push-pop", "interactive"})
    String mode = "push-pop";

    Yices2Parameters(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
      if (logic == null && solverType.equals("mcsat") && !mode.equals("push-pop")) {
        // Yices2 ignores the mode in this case, and always uses 'push-pop'
        throw new InvalidConfigurationException(
            ("Yices2 only supports the mode 'push-pop' for MCSAT without a logic, but"
                    + " solver.yices2.mode is '%s'. Use the mode 'push-pop', set"
                    + " solver.yices2.solverType to 'dpllt', or set a logic with"
                    + " solver.yices2.logic.")
                .formatted(mode));
      }
    }

    /** Whether Yices2 uses MCSAT for this configuration, see logic2arch in Yices2. */
    boolean usesMcsat() {
      if (logic == null) {
        return solverType.equals("mcsat");
      }
      return logic.contains("NIA")
          || logic.contains("NRA")
          || logic.contains("NIRA")
          || logic.equals("QF_FFA");
    }
  }

  private final Yices2FormulaCreator creator;
  private final BooleanFormulaManager bfmgr;
  private final ShutdownNotifier shutdownManager;
  private final Yices2Parameters parameters;

  private static int numLoadedInstances = 0;
  private boolean closed = false;

  private Yices2SolverContext(
      FormulaManager pFmgr,
      Yices2FormulaCreator creator,
      BooleanFormulaManager pBfmgr,
      ShutdownNotifier pShutdownManager,
      Yices2Parameters pParameters) {
    super(pFmgr);
    this.creator = creator;
    bfmgr = pBfmgr;
    shutdownManager = pShutdownManager;
    parameters = pParameters;
  }

  public static Yices2SolverContext create(
      Configuration pConfig,
      NonLinearArithmetic pNonLinearArithmetic,
      ShutdownNotifier pShutdownManager,
      Consumer<String> pLoader)
      throws InvalidConfigurationException {

    pLoader.accept("yices2java");

    synchronized (Yices2SolverContext.class) {
      if (numLoadedInstances == 0) {
        // Avoid loading and initializing twice,
        // because this would make all existing terms and types unavailable,
        // which is bad behavior and a potential memory leak.
        System.setProperty("yices.skipAutoloader", "true");
        Yices.isReady();
      }
      numLoadedInstances++;
    }

    Yices2Parameters params = new Yices2Parameters(pConfig);

    Yices2FormulaCreator creator = new Yices2FormulaCreator();
    Yices2UFManager functionTheory = new Yices2UFManager(creator);
    Yices2BooleanFormulaManager booleanTheory = new Yices2BooleanFormulaManager(creator);
    Yices2BitvectorFormulaManager bitvectorTheory =
        new Yices2BitvectorFormulaManager(creator, booleanTheory);
    // Only MCSAT supports non-linear arithmetic
    Yices2IntegerFormulaManager integerTheory =
        new Yices2IntegerFormulaManager(creator, pNonLinearArithmetic, params.usesMcsat());
    Yices2RationalFormulaManager rationalTheory =
        new Yices2RationalFormulaManager(creator, pNonLinearArithmetic, params.usesMcsat());
    Yices2QuantifiedFormulaManager quantTheory = new Yices2QuantifiedFormulaManager(creator);
    Yices2ArrayFormulaManager arrayTheory = new Yices2ArrayFormulaManager(creator);
    Yices2FormulaManager manager =
        new Yices2FormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory,
            quantTheory,
            arrayTheory);
    return new Yices2SolverContext(manager, creator, booleanTheory, pShutdownManager, params);
  }

  @Override
  public String getVersion() {
    return "Yices " + Yices.version();
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.YICES2;
  }

  @Override
  public synchronized void close() {
    if (!closed) {
      closed = true;
      synchronized (Yices2SolverContext.class) {
        numLoadedInstances--;
        if (numLoadedInstances == 0) {
          // TODO Garbage collect?
        }
      }
    }
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    return new Yices2Prover(creator, pOptions, bfmgr, shutdownManager, parameters);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pOptions) {
    return new Yices2InterpolatingProver(creator, pOptions, bfmgr, shutdownManager, parameters);
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("Yices does not support optimization");
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }
}
