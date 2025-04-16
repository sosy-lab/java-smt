// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;
import java.util.function.Consumer;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
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

  @Override
  public final ProverEnvironment newProverEnvironment(ProverOptions... options) {
    ProverEnvironment out = newProverEnvironment0(toSet(options));
    if (!supportsAssumptionSolving()) {
      // In the case we do not already have a prover environment with assumptions,
      // we add a wrapper to it
      out = new ProverWithAssumptionsWrapper(out);
    }
    return out;
  }

  protected abstract ProverEnvironment newProverEnvironment0(Set<ProverOptions> options);

  @SuppressWarnings("resource")
  @Override
  public final InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... options) {

    InterpolatingProverEnvironment<?> out = newProverEnvironmentWithInterpolation1(toSet(options));
    if (!supportsAssumptionSolving()) {
      // In the case we do not already have a prover environment with assumptions,
      // we add a wrapper to it
      out = new InterpolatingProverWithAssumptionsWrapper<>(out, fmgr);
    }
    return out;
  }

  // TODO: would it be better to add the option for interpolation procedure based on the call to
  //  getInterpolant() and always use the wrapper as long as there is a option?
  //  If this remains, clean it up!
  @SuppressWarnings({"CheckReturnValue", "resource"})
  private InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation1(
      Set<ProverOptions> options) {
    InterpolatingProverEnvironment<?> out;
    // Try to get a new prover environment w native interpolation with the current options
    try {
      out = newProverEnvironmentWithInterpolation0(options);
    } catch (UnsupportedOperationException e) {
      // If native interpolation fails, we check the options for independent interpolation and
      // return a wrapped normal prover with independent interpolation, as long as the prover
      // supports the option chosen.
      String additionalMsg = ". You can try to use a independent interpolation strategy.";
      try {
        if (!useNativeInterpolation(options)) {
          if (getIndependentInterpolationStrategy(options)
                  == ProverOptions.GENERATE_UNIFORM_FORWARD_INTERPOLANTS
              || getIndependentInterpolationStrategy(options)
                  == ProverOptions.GENERATE_UNIFORM_BACKWARD_INTERPOLANTS) {
            fmgr.getQuantifiedFormulaManager()
                .eliminateQuantifiers(fmgr.getBooleanFormulaManager().makeTrue());
          }
          return new IndependentInterpolatingSolverDelegate(
              this, newProverEnvironment0(options), options);
        }
      } catch (UnsupportedOperationException e2) {
        // Solver does not support independent interpolation
        additionalMsg =
            ". Interpolation strategy "
                + getIndependentInterpolationStrategy(options)
                + " is not "
                + "available "
                + "due to: "
                + e2.getMessage();
      } catch (SolverException | InterruptedException pE) {
        // Should never happen as we only run the solver briefly to determine feature availability
        throw new RuntimeException(pE);
      }
      // Build a nice message with additional info
      throw new UnsupportedOperationException(e.getMessage() + additionalMsg);
    }

    if (!useNativeInterpolation(options)) {
      // The user may choose to use independent interpolation on top of native
      out = new IndependentInterpolatingSolverDelegate(this, out, options);
    }
    return out;
  }

  protected abstract InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pSet);

  @SuppressWarnings("resource")
  @Override
  public final OptimizationProverEnvironment newOptimizationProverEnvironment(
      ProverOptions... options) {
    return newOptimizationProverEnvironment0(toSet(options));
  }

  protected abstract OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet);

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

  private static final Set<ProverOptions> ALL_INDEPENDENT_INTERPOLATION_STRATEGIES =
      ImmutableSet.of(
          ProverOptions.GENERATE_PROJECTION_BASED_INTERPOLANTS,
          ProverOptions.GENERATE_UNIFORM_BACKWARD_INTERPOLANTS,
          ProverOptions.GENERATE_UNIFORM_FORWARD_INTERPOLANTS);

  protected boolean useNativeInterpolation(Set<ProverOptions> options) {
    return getIndependentInterpolationStrategy(options) == null;
  }

  @SuppressWarnings("CheckReturnValue")
  protected @Nullable ProverOptions getIndependentInterpolationStrategy(
      Set<ProverOptions> options) {
    List<ProverOptions> itpStrat = new ArrayList<>(options);
    itpStrat.retainAll(ALL_INDEPENDENT_INTERPOLATION_STRATEGIES);

    if (itpStrat.isEmpty()) {
      return null;
    } else if (itpStrat.size() != 1) {
      throw new IllegalArgumentException(
          "Only a single independent interpolation strategy can be"
              + " chosen for a prover, but chosen were: "
              + Joiner.on(", ").join(options));
    }

    ProverOptions interpolationOption = itpStrat.get(0);
    try {
      fmgr.getQuantifiedFormulaManager();
    } catch (UnsupportedOperationException e) {
      throw new UnsupportedOperationException(
          "Solver does not support independent interpolation based on the current strategy, as"
              + " it is lacking quantifier support.");
    }
    return interpolationOption;
  }

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
