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
  private static class Yices2Parameters {
    @Option(
        secure = true,
        description = "Backend to use for the solver",
        values = {"dpllt", "mcsat"})
    String solverType = "mcsat";

    Yices2Parameters(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
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
    Yices2IntegerFormulaManager integerTheory =
        new Yices2IntegerFormulaManager(creator, pNonLinearArithmetic);
    Yices2RationalFormulaManager rationalTheory =
        new Yices2RationalFormulaManager(creator, pNonLinearArithmetic);
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
    return new Yices2Prover(creator, pOptions, bfmgr, shutdownManager, parameters.solverType);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pOptions) {
    return new Yices2InterpolatingProver(
        creator, pOptions, bfmgr, shutdownManager, parameters.solverType);
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("Yices does not support optimization");
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return true;
  }
}
