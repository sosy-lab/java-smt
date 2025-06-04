// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;
import java.util.function.Consumer;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.withAssumptionsWrapper.InterpolatingProverWithAssumptionsWrapper;
import org.sosy_lab.java_smt.basicimpl.withAssumptionsWrapper.ProverWithAssumptionsWrapper;

public abstract class AbstractSolverContext implements SolverContext {

  private final FormulaManager fmgr;

  protected AbstractSolverContext(FormulaManager fmgr) {
    this.fmgr = fmgr;
  }

  @Override
  public final FormulaManager getFormulaManager() {
    return fmgr;
  }

  @SuppressWarnings("resource")
  @Override
  public final ProverEnvironment newProverEnvironment(ProverOptions... options) {
    ProverEnvironment out = newProverEnvironment0(null, toSet(options));
    return wrapProverEnvironmentWithAssumptionsWrapper(out);
  }

  @SuppressWarnings("resource")
  @Override
  public final ProverEnvironment newProverEnvironment(
      ShutdownNotifier pProverShutdownNotifier, ProverOptions... options) {
    ProverEnvironment out = newProverEnvironment0(pProverShutdownNotifier, toSet(options));
    return wrapProverEnvironmentWithAssumptionsWrapper(out);
  }

  // TODO: switch to 2 methods with a default exception for pProverShutdownNotifier?
  protected abstract ProverEnvironment newProverEnvironment0(
      @Nullable ShutdownNotifier pProverShutdownNotifier, Set<ProverOptions> options);

  private ProverEnvironment wrapProverEnvironmentWithAssumptionsWrapper(
      ProverEnvironment pProverEnvironment) {
    if (!supportsAssumptionSolving()) {
      // In the case we do not already have a prover environment with assumptions,
      // we add a wrapper to it
      return new ProverWithAssumptionsWrapper(pProverEnvironment);
    }
    return pProverEnvironment;
  }

  @SuppressWarnings("resource")
  @Override
  public final InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... options) {

    InterpolatingProverEnvironment<?> out =
        newProverEnvironmentWithInterpolation0(null, toSet(options));
    return wrapProverEnvironmentWithAssumptionsWrapper(out);
  }

  @SuppressWarnings("resource")
  @Override
  public final InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ShutdownNotifier pProverShutdownNotifier, ProverOptions... options) {

    InterpolatingProverEnvironment<?> out =
        newProverEnvironmentWithInterpolation0(pProverShutdownNotifier, toSet(options));
    return wrapProverEnvironmentWithAssumptionsWrapper(out);
  }

  // TODO: switch to 2 methods with a default exception for pProverShutdownNotifier?
  protected abstract InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      @Nullable ShutdownNotifier pProverShutdownNotifier, Set<ProverOptions> pSet);

  private InterpolatingProverEnvironment<?> wrapProverEnvironmentWithAssumptionsWrapper(
      InterpolatingProverEnvironment<?> pInterpolatingProverEnvironment) {
    if (!supportsAssumptionSolving()) {
      // In the case we do not already have a prover environment with assumptions,
      // we add a wrapper to it
      return new InterpolatingProverWithAssumptionsWrapper<>(pInterpolatingProverEnvironment, fmgr);
    }
    return pInterpolatingProverEnvironment;
  }

  @SuppressWarnings("resource")
  @Override
  public final OptimizationProverEnvironment newOptimizationProverEnvironment(
      ProverOptions... options) {
    return newOptimizationProverEnvironment0(null, toSet(options));
  }

  @SuppressWarnings("resource")
  @Override
  public final OptimizationProverEnvironment newOptimizationProverEnvironment(
      ShutdownNotifier pProverShutdownNotifier, ProverOptions... options) {
    return newOptimizationProverEnvironment0(pProverShutdownNotifier, toSet(options));
  }

  // TODO: switch to 2 methods with a default exception for pProverShutdownNotifier?
  protected abstract OptimizationProverEnvironment newOptimizationProverEnvironment0(
      @Nullable ShutdownNotifier pProverShutdownNotifier, Set<ProverOptions> pSet);

  /**
   * Whether the solver supports solving under some given assumptions (with all corresponding
   * features) by itself, i.e., whether {@link
   * ProverEnvironment#isUnsatWithAssumptions(java.util.Collection)} and {@link
   * InterpolatingProverEnvironment#isUnsatWithAssumptions(java.util.Collection)} are fully
   * implemented.
   *
   * <p>Otherwise, i.e., if this method returns {@code false}, the solver does not need to support
   * this feature and may simply {@code throw UnsupportedOperationException} in the respective
   * methods. This class will wrap the prover environments and provide an implementation of the
   * feature.
   *
   * <p>This method is expected to always return the same value. Otherwise, the behavior of this
   * class is undefined.
   */
  protected abstract boolean supportsAssumptionSolving();

  private static Set<ProverOptions> toSet(ProverOptions... options) {
    Set<ProverOptions> opts = EnumSet.noneOf(ProverOptions.class);
    Collections.addAll(opts, options);
    return opts;
  }

  /**
   * This method loads the given libraries.
   *
   * <p>If the first list of libraries can not be loaded, the second list is used as a fallback. The
   * two lists of libraries can be used to differ between libraries specific to Unix/Linux and
   * Windows.
   *
   * <p>If the first try aborts after a few steps, we do not clean up partially loaded libraries,
   * but directly start the second try.
   *
   * <p>Each list is applied in the given ordering.
   *
   * @param loader the loading mechanism that will be used for loading each single library.
   * @param librariesForFirstTry list of library names that will be loaded, if possible.
   * @param librariesForSecondTry list of library names that will be loaded, after the first attempt
   *     (using librariesForFirstTry) has failed.
   * @throws UnsatisfiedLinkError if neither the first nor second try returned a successful loading
   *     process.
   */
  protected static void loadLibrariesWithFallback(
      Consumer<String> loader,
      List<String> librariesForFirstTry,
      List<String> librariesForSecondTry)
      throws UnsatisfiedLinkError {
    Preconditions.checkNotNull(librariesForFirstTry);
    Preconditions.checkNotNull(librariesForSecondTry);
    try {
      librariesForFirstTry.forEach(loader);
    } catch (UnsatisfiedLinkError e1) {
      try {
        librariesForSecondTry.forEach(loader);
      } catch (UnsatisfiedLinkError e2) {
        e1.addSuppressed(e2);
        throw e1;
      }
    }
  }
}
