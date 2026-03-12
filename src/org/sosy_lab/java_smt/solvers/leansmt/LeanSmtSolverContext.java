// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import java.util.Set;
import java.util.function.Consumer;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

/**
 * LeanSMT solver context implementation.
 *
 * <p>Threading contract: one context/prover must not be used concurrently from multiple threads.
 * Sequential handoff across threads is supported.
 */
public final class LeanSmtSolverContext extends AbstractSolverContext {

  private final LeanSmtFormulaCreator creator;
  private final BooleanFormulaManager bfmgr;
  private final ShutdownNotifier shutdownNotifier;
  private final String logic;

  private static int numLoadedInstances = 0;
  private static boolean initialized = false;
  private boolean closed = false;

  private LeanSmtSolverContext(
      FormulaManager pFmgr,
      LeanSmtFormulaCreator pCreator,
      BooleanFormulaManager pBfmgr,
      ShutdownNotifier pShutdownNotifier,
      String pLogic) {
    super(pFmgr);
    creator = pCreator;
    bfmgr = pBfmgr;
    shutdownNotifier = pShutdownNotifier;
    logic = pLogic;
  }

  public static LeanSmtSolverContext create(
      ShutdownNotifier pShutdownNotifier,
      NonLinearArithmetic pNonLinearArithmetic,
      Consumer<String> pLoader)
      throws InvalidConfigurationException {
    return create(
        pShutdownNotifier,
        pNonLinearArithmetic,
        pLoader,
        /* pAllowBundledLibraryFallback= */ true);
  }

  public static LeanSmtSolverContext create(
      ShutdownNotifier pShutdownNotifier,
      NonLinearArithmetic pNonLinearArithmetic,
      Consumer<String> pLoader,
      boolean pAllowBundledLibraryFallback)
      throws InvalidConfigurationException {

    long constructionSolver = 0L;
    try {
      synchronized (LeanSmtSolverContext.class) {
        if (!initialized) {
          LeanSmtNativeApi.loadLibrary(pLoader, pAllowBundledLibraryFallback);
          LeanSmtNativeApi.initialize();
          initialized = true;
        }
      }

      constructionSolver = LeanSmtNativeApi.createSolverCvc5();
      String logic = "ALL";
      LeanSmtNativeApi.setLogic(constructionSolver, logic);

      LeanSmtFormulaCreator creator = new LeanSmtFormulaCreator(constructionSolver);
      LeanSmtUFManager ufManager = new LeanSmtUFManager(creator);
      LeanSmtBooleanFormulaManager booleanTheory = new LeanSmtBooleanFormulaManager(creator);
      LeanSmtIntegerFormulaManager integerTheory =
          new LeanSmtIntegerFormulaManager(creator, pNonLinearArithmetic);
      LeanSmtRationalFormulaManager rationalTheory =
          new LeanSmtRationalFormulaManager(creator, pNonLinearArithmetic);
      LeanSmtBitvectorFormulaManager bitvectorTheory =
          new LeanSmtBitvectorFormulaManager(creator, booleanTheory);
      LeanSmtFormulaManager manager =
          new LeanSmtFormulaManager(
              creator, ufManager, booleanTheory, integerTheory, rationalTheory, bitvectorTheory);

      synchronized (LeanSmtSolverContext.class) {
        numLoadedInstances++;
      }
      return new LeanSmtSolverContext(manager, creator, booleanTheory, pShutdownNotifier, logic);
    } catch (SolverException e) {
      if (constructionSolver != 0L) {
        LeanSmtNativeApi.deleteSolverAsync(constructionSolver);
      }
      synchronized (LeanSmtSolverContext.class) {
        if (initialized && !LeanSmtNativeApi.isNativeRuntimeInitialized()) {
          initialized = false;
        }
      }
      throw new InvalidConfigurationException("Failed to initialize LeanSMT backend", e);
    } catch (RuntimeException e) {
      if (constructionSolver != 0L) {
        LeanSmtNativeApi.deleteSolverAsync(constructionSolver);
      }
      throw e;
    }
  }

  @Override
  public String getVersion() {
    return "LeanSMT 1.0";
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.LEANSMT;
  }

  @Override
  public synchronized void close() {
    if (!closed) {
      closed = true;
      // Best-effort cleanup for construction solver; this context no longer needs it.
      LeanSmtNativeApi.deleteSolverAsync(creator.getConstructionSolver());
      synchronized (LeanSmtSolverContext.class) {
        numLoadedInstances--;
        if (numLoadedInstances == 0) {
          // Native global cleanup can block in some environments.
          // Keep runtime initialized for process lifetime.
        }
      }
    }
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    return new LeanSmtTheoremProver(creator, pOptions, bfmgr, shutdownNotifier, logic);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("LeanSMT backend does not support interpolation");
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("LeanSMT backend does not support optimization");
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return true;
  }
}
