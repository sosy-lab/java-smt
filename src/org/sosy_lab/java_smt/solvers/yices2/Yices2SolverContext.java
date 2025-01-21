// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.basicimpl.IndependentInterpolatingProverEnvironment.hasIndependentInterpolationStrategy;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_exit;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_major_version;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_patch_level;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_version;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_init;

import java.util.Set;
import java.util.function.Consumer;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.basicimpl.IndependentInterpolatingProverEnvironment;

public class Yices2SolverContext extends AbstractSolverContext {

  private final Yices2FormulaCreator creator;
  private final FormulaManager fmgr;
  private final ShutdownNotifier shutdownManager;

  private static int numLoadedInstances = 0;
  private boolean closed = false;

  public Yices2SolverContext(
      FormulaManager pFmgr, Yices2FormulaCreator creator, ShutdownNotifier pShutdownManager) {
    super(pFmgr);
    fmgr = pFmgr;
    this.creator = creator;
    shutdownManager = pShutdownManager;
  }

  public static Yices2SolverContext create(
      NonLinearArithmetic pNonLinearArithmetic,
      ShutdownNotifier pShutdownManager,
      Consumer<String> pLoader) {

    pLoader.accept("yices2j");

    synchronized (Yices2SolverContext.class) {
      if (numLoadedInstances == 0) {
        // Avoid loading and initializing twice,
        // because this would make all existing terms and types unavailable,
        // which is bad behavior and a potential memory leak.
        yices_init();
      }
      numLoadedInstances++;
    }

    Yices2FormulaCreator creator = new Yices2FormulaCreator();
    Yices2UFManager functionTheory = new Yices2UFManager(creator);
    Yices2BooleanFormulaManager booleanTheory = new Yices2BooleanFormulaManager(creator);
    Yices2BitvectorFormulaManager bitvectorTheory =
        new Yices2BitvectorFormulaManager(creator, booleanTheory);
    Yices2IntegerFormulaManager integerTheory =
        new Yices2IntegerFormulaManager(creator, pNonLinearArithmetic);
    Yices2RationalFormulaManager rationalTheory =
        new Yices2RationalFormulaManager(creator, pNonLinearArithmetic);
    Yices2QuantifiedFormulaManager quantifiedFormulaManager =
        new Yices2QuantifiedFormulaManager(creator);

    Yices2FormulaManager manager =
        new Yices2FormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory,
            quantifiedFormulaManager);
    return new Yices2SolverContext(manager, creator, pShutdownManager);
  }

  @Override
  public String getVersion() {
    return String.format(
        "Yices %d.%d.%d", yices_get_version(), yices_get_major_version(), yices_get_patch_level());
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
          yices_exit();
        }
      }
    }
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    return new Yices2TheoremProver(creator, pOptions, fmgr, shutdownManager);
  }

  @SuppressWarnings("resource")
  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> options) {
    if (!hasIndependentInterpolationStrategy(options)) {
      throw new UnsupportedOperationException(
          "Yices2 does not support interpolation natively. Try "
              + "using the independent interpolation options GENERATE_MODEL_BASED_INTERPOLANTS,"
              + " GENERATE_UNIFORM_BACKWARD_INTERPOLANTS, GENERATE_UNIFORM_FORWARD_INTERPOLANTS.");
    }
    return new IndependentInterpolatingProverEnvironment<>(
        this, creator, newProverEnvironment0(options), options);
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
