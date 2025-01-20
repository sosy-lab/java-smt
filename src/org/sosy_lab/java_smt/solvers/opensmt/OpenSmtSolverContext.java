// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;


import com.google.common.base.Preconditions;
import java.util.Set;
import java.util.function.Consumer;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.basicimpl.IndependentInterpolatingProverEnvironment;
import org.sosy_lab.java_smt.solvers.opensmt.api.LogicFactory;

public class OpenSmtSolverContext extends AbstractSolverContext {
  private final OpenSmtFormulaCreator creator;
  private final OpenSmtFormulaManager manager;

  @SuppressWarnings("unused")
  private final LogManager logger;

  private final ShutdownNotifier shutdownNotifier;
  private final OpenSMTOptions solverOptions;

  private boolean closed = false;

  @Options(prefix = "solver.opensmt")
  static class OpenSMTOptions {

    @Option(secure = true, description = "SMT-LIB2 name of the logic to be used by the solver.")
    Logics logic = Logics.QF_AUFLIRA;

    @Option(secure = true, description = "Algorithm for boolean interpolation")
    int algBool = 0;

    @Option(secure = true, description = "Algorithm for UF interpolation")
    int algUf = 0;

    @Option(secure = true, description = "Algorithm for LRA interpolation")
    int algLra = 0;

    final int randomSeed;

    OpenSMTOptions(Configuration config, int pRandomSeed) throws InvalidConfigurationException {
      config.inject(this);
      randomSeed = pRandomSeed;
    }
  }

  private OpenSmtSolverContext(
      OpenSmtFormulaCreator pCreator,
      OpenSmtFormulaManager pManager,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      OpenSMTOptions pSolverOptions) {

    super(pManager);
    creator = pCreator;
    manager = pManager;
    logger = pLogger;
    shutdownNotifier = pShutdownNotifier;
    solverOptions = pSolverOptions;
  }

  public static SolverContext create(
      Configuration config,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      long pRandom,
      NonLinearArithmetic pNonLinearArithmetic,
      Consumer<String> pLoader)
      throws InvalidConfigurationException {

    // Make sure the native libraries are loaded
    pLoader.accept("opensmt");
    pLoader.accept("opensmtjava");

    OpenSMTOptions solverOptions = new OpenSMTOptions(config, (int) pRandom);

    // Instantiate OpenSmtFormulaCreator to open a new solver instance
    OpenSmtFormulaCreator creator = OpenSmtFormulaCreator.create(solverOptions.logic);

    // Create all formula managers
    OpenSmtUFManager functionTheory = new OpenSmtUFManager(creator);
    OpenSmtBooleanFormulaManager booleanTheory = new OpenSmtBooleanFormulaManager(creator);
    OpenSmtIntegerFormulaManager integerTheory =
        new OpenSmtIntegerFormulaManager(creator, pNonLinearArithmetic);
    OpenSmtRationalFormulaManager rationalTheory =
        new OpenSmtRationalFormulaManager(creator, pNonLinearArithmetic);
    OpenSmtArrayFormulaManager arrayTheory = new OpenSmtArrayFormulaManager(creator);

    // Build the central FormulaManager object
    OpenSmtFormulaManager manager =
        new OpenSmtFormulaManager(
            creator, functionTheory, booleanTheory, integerTheory, rationalTheory, arrayTheory);

    return new OpenSmtSolverContext(creator, manager, pLogger, pShutdownNotifier, solverOptions);
  }

  @Override
  public void close() {
    if (!closed) {
      closed = true;
      creator.getEnv().delete();
    }
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.OPENSMT;
  }

  @Override
  public String getVersion() {
    return "OpenSMT " + LogicFactory.getVersion();
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<SolverContext.ProverOptions> options) {
    throw new UnsupportedOperationException("OpenSMT does not support optimization.");
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(
      Set<SolverContext.ProverOptions> pProverOptions) {
    Preconditions.checkState(!closed, "solver context is already closed");
    return new OpenSmtTheoremProver(
        creator, manager, shutdownNotifier, pProverOptions, solverOptions);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<SolverContext.ProverOptions> options) {
    Preconditions.checkState(!closed, "solver context is already closed");
    return new IndependentInterpolatingProverEnvironment<>(
        this,
        creator,
        new OpenSmtInterpolatingProver(creator, manager, shutdownNotifier, options, solverOptions),
        options,
        shutdownNotifier);
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }
}
