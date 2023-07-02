// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import com.google.common.base.Preconditions;
import java.util.Set;
import java.util.function.Consumer;
import opensmt.OpenSmt;
import opensmt.opensmt_logic;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public class OpenSmtSolverContext extends AbstractSolverContext {
  private final OpenSmtFormulaCreator creator;
  private final OpenSmtFormulaManager manager;

  @SuppressWarnings("unused")
  private final LogManager logger;

  private final ShutdownNotifier shutdownNotifier;

  private boolean closed = false;

  private OpenSmtSolverContext(
      OpenSmtFormulaCreator pCreator,
      OpenSmtFormulaManager pManager,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier) {

    super(pManager);
    creator = pCreator;
    manager = pManager;
    logger = pLogger;
    shutdownNotifier = pShutdownNotifier;
  }

  public static SolverContext create(
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      long randomSeed,
      NonLinearArithmetic pNonLinearArithmetic,
      Consumer<String> pLoader) {

    // Make sure the native libraries are loaded
    pLoader.accept("opensmt");
    pLoader.accept("opensmtjava");

    // Create a solver instance
    OpenSmt newSolver = new OpenSmt(opensmt_logic.qf_auflira, "javasmt", false);
    newSolver.getConfig().setRandomSeed((int) randomSeed);
    
    OpenSmtFormulaCreator creator = new OpenSmtFormulaCreator(newSolver);

    // Create managers
    OpenSmtUFManager functionTheory = new OpenSmtUFManager(creator);
    OpenSmtBooleanFormulaManager booleanTheory = new OpenSmtBooleanFormulaManager(creator);
    OpenSmtIntegerFormulaManager integerTheory =
        new OpenSmtIntegerFormulaManager(creator, pNonLinearArithmetic);
    OpenSmtRationalFormulaManager rationalTheory =
        new OpenSmtRationalFormulaManager(creator, pNonLinearArithmetic);
    OpenSmtArrayFormulaManager arrayTheory = new OpenSmtArrayFormulaManager(creator);

    OpenSmtFormulaManager manager =
        new OpenSmtFormulaManager(
            creator, functionTheory, booleanTheory, integerTheory, rationalTheory, arrayTheory);

    return new OpenSmtSolverContext(creator, manager, pLogger, pShutdownNotifier);
  }

  @Override
  public void close() {
    if (creator != null) {
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
    // FIXME: OpenSMT does not provide a way to read the version number. We'll have to patch the source or get it from the lib
    throw new UnsupportedOperationException();
  }
  
  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<SolverContext.ProverOptions> options) {
    throw new UnsupportedOperationException("OpenSMT does not support optimization.");
  }
  
  @Override
  protected ProverEnvironment newProverEnvironment0(Set<SolverContext.ProverOptions> options) {
    Preconditions.checkState(!closed, "solver context is already closed");
    return new OpenSmtTheoremProver(creator, manager, shutdownNotifier, options);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<SolverContext.ProverOptions> options) {
    Preconditions.checkState(!closed, "solver context is already closed");
    return new OpenSmtInterpolatingProver(creator, manager, shutdownNotifier, options);
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }
}
