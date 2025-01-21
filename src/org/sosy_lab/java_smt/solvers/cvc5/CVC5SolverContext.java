// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.Preconditions;
import io.github.cvc5.Solver;
import java.util.Set;
import java.util.function.Consumer;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.basicimpl.IndependentInterpolatingProverEnvironment;

public final class CVC5SolverContext extends AbstractSolverContext {

  @Options(prefix = "solver.cvc5")
  private static class CVC5Settings {

    @Option(
        secure = true,
        description = "apply additional validation checks for interpolation results")
    private boolean validateInterpolants = false;

    private CVC5Settings(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
    }
  }

  // creator is final, except after closing, then null.
  private CVC5FormulaCreator creator;
  private final Solver solver;
  private final ShutdownNotifier shutdownNotifier;
  private final int randomSeed;
  private final CVC5Settings settings;
  private boolean closed = false;

  private CVC5SolverContext(
      CVC5FormulaCreator pCreator,
      CVC5FormulaManager pManager,
      ShutdownNotifier pShutdownNotifier,
      Solver pSolver,
      int pRandomSeed,
      CVC5Settings pSettings) {
    super(pManager);
    creator = pCreator;
    shutdownNotifier = pShutdownNotifier;
    randomSeed = pRandomSeed;
    solver = pSolver;
    settings = pSettings;
  }

  @VisibleForTesting
  static void loadLibrary(Consumer<String> pLoader) {
    pLoader.accept("cvc5jni");

    // disable CVC5's own loading mechanism,
    // see io.github.cvc5.Util#loadLibraries and https://github.com/cvc5/cvc5/pull/9047
    System.setProperty("cvc5.skipLibraryLoad", "true");
  }

  @SuppressWarnings({"unused", "resource"})
  public static SolverContext create(
      LogManager pLogger,
      Configuration pConfig,
      ShutdownNotifier pShutdownNotifier,
      int randomSeed,
      NonLinearArithmetic pNonLinearArithmetic,
      FloatingPointRoundingMode pFloatingPointRoundingMode,
      Consumer<String> pLoader)
      throws InvalidConfigurationException {

    CVC5Settings settings = new CVC5Settings(pConfig);

    loadLibrary(pLoader);

    // This Solver is the central class for creating expressions/terms/formulae.
    // We keep this instance available until the whole context is closed.
    Solver newSolver = new Solver();

    setSolverOptions(newSolver, randomSeed);

    CVC5FormulaCreator pCreator = new CVC5FormulaCreator(newSolver);

    // Create managers
    CVC5UFManager functionTheory = new CVC5UFManager(pCreator);
    CVC5BooleanFormulaManager booleanTheory = new CVC5BooleanFormulaManager(pCreator);
    CVC5IntegerFormulaManager integerTheory =
        new CVC5IntegerFormulaManager(pCreator, pNonLinearArithmetic);
    CVC5RationalFormulaManager rationalTheory =
        new CVC5RationalFormulaManager(pCreator, pNonLinearArithmetic);
    CVC5BitvectorFormulaManager bitvectorTheory =
        new CVC5BitvectorFormulaManager(pCreator, booleanTheory);
    CVC5FloatingPointFormulaManager fpTheory =
        new CVC5FloatingPointFormulaManager(pCreator, pFloatingPointRoundingMode);
    CVC5QuantifiedFormulaManager qfTheory = new CVC5QuantifiedFormulaManager(pCreator);
    CVC5ArrayFormulaManager arrayTheory = new CVC5ArrayFormulaManager(pCreator);
    CVC5SLFormulaManager slTheory = new CVC5SLFormulaManager(pCreator);
    CVC5StringFormulaManager strTheory = new CVC5StringFormulaManager(pCreator);
    CVC5EnumerationFormulaManager enumTheory = new CVC5EnumerationFormulaManager(pCreator);
    CVC5FormulaManager manager =
        new CVC5FormulaManager(
            pCreator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory,
            fpTheory,
            qfTheory,
            arrayTheory,
            slTheory,
            strTheory,
            enumTheory);

    return new CVC5SolverContext(
        pCreator, manager, pShutdownNotifier, newSolver, randomSeed, settings);
  }

  /** Set common options for a CVC5 solver. */
  private static void setSolverOptions(Solver pSolver, int randomSeed) {
    pSolver.setOption("seed", String.valueOf(randomSeed));
    pSolver.setOption("output-language", "smtlib2");

    // Set Strings option to enable all String features (such as lessOrEquals).
    // This should not have any effect for non-string theories.
    // pSolver.setOption("strings-exp", "true");

    // pSolver.setOption("finite-model-find", "true");
    // pSolver.setOption("sets-ext", "true");

    // pSolver.setOption("produce-models", "true");
    // pSolver.setOption("produce-unsat-cores", "true");

    // Neither simplification, arith-rewrite-equalities, pb-rewrites provide rewrites of trivial
    // formulas only.
    // Note: with solver.getOptionNames() you can get all options
  }

  @Override
  public String getVersion() {
    String version = solver.getInfo("version");
    if (version.startsWith("\"") && version.endsWith("\"")) {
      version = version.substring(1, version.length() - 1);
    }
    return "CVC5 " + version;
  }

  @Override
  public void close() {
    if (creator != null) {
      closed = true;
      solver.deletePointer();
      // Don't use Context.deletePointers(); as it deletes statically information from all
      // existing contexts, not only this one!
      creator = null;
    }
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.CVC5;
  }

  @Override
  public ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    Preconditions.checkState(!closed, "solver context is already closed");
    return new CVC5TheoremProver(
        creator, shutdownNotifier, randomSeed, pOptions, getFormulaManager());
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> options) {
    Preconditions.checkState(!closed, "solver context is already closed");

    CVC5InterpolatingProver itpProver =
        new CVC5InterpolatingProver(
            creator,
            shutdownNotifier,
            randomSeed,
            options,
            getFormulaManager(),
            settings.validateInterpolants);

    return new IndependentInterpolatingProverEnvironment<>(this, creator, itpProver, options);
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("CVC5 does not support optimization");
  }
}
