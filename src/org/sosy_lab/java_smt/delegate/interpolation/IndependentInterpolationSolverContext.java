/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.interpolation;

import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;

@Options
public class IndependentInterpolationSolverContext implements SolverContext {
  public enum InterpolationMethod {
    /** Rely on the solver for calculating interpolants. */
    SOLVER,

    /**
     * Enables Craig interpolation, using the model-based interpolation strategy. This strategy
     * constructs interpolants based on the model provided by a solver, i.e. model generation must
     * be enabled. This interpolation strategy is only usable for solvers supporting quantified
     * solving over the theories interpolated upon. The solver does not need to support
     * interpolation itself.
     */
    MODEL_PROJECTION,

    /**
     * Enables (uniform) Craig interpolation, using the quantifier-based interpolation strategy
     * utilizing quantifier-elimination in the forward direction. Forward means, that the set of
     * formulas A, used to interpolate, interpolates towards the set of formulas B (B == all
     * formulas that are currently asserted, but not in the given set of formulas A used to
     * interpolate). This interpolation strategy is only usable for solvers supporting
     * quantifier-elimination over the theories interpolated upon. The solver does not need to
     * support interpolation itself.
     */
    QUANTIFIER_ELIMINATION_FORWARD,

    /**
     * Enables (uniform) Craig interpolation, using the quantifier-based interpolation strategy
     * utilizing quantifier-elimination in the backward direction. Backward means, that the set of
     * formulas B (B == all formulas that are currently asserted, but not in the given set of
     * formulas A used to interpolate) interpolates towards the set of formulas A. This
     * interpolation strategy is only usable for solvers supporting quantifier-elimination over the
     * theories interpolated upon. The solver does not need to support interpolation itself.
     */
    QUANTIFIER_ELIMINATION_BACKWARD
  }

  @Option(
      secure = true,
      name = "solver.interpolation.method",
      description = "Selects how interpolants are generated.")
  private InterpolationMethod interpolationMethod =
      InterpolationMethod.QUANTIFIER_ELIMINATION_FORWARD;

  private final SolverContext delegate;

  public IndependentInterpolationSolverContext(
      Configuration pConfiguration, SolverContext pDelegate) throws InvalidConfigurationException {
    pConfiguration.inject(this);
    delegate = pDelegate;
  }

  @Override
  public FormulaManager getFormulaManager() {
    return delegate.getFormulaManager();
  }

  @Override
  public ProverEnvironment newProverEnvironment(ProverOptions... options) {
    return delegate.newProverEnvironment(options);
  }

  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... options) {
    if (interpolationMethod == InterpolationMethod.SOLVER) {
      return delegate.newProverEnvironmentWithInterpolation(options);
    } else {
      return new IndependentInterpolationProverEnvironment(
          this, interpolationMethod, delegate.newProverEnvironment(options));
    }
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(ProverOptions... options) {
    return delegate.newOptimizationProverEnvironment(options);
  }

  @Override
  public String getVersion() {
    return delegate.getVersion();
  }

  @Override
  public SolverContextFactory.Solvers getSolverName() {
    return delegate.getSolverName();
  }

  @Override
  public void close() {
    delegate.close();
  }
}
