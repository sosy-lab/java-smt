// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.common.collect.ImmutableMap;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

/**
 * Instances of this interface provide access to an SMT solver. A single SolverContext should be
 * used only from a single thread.
 *
 * <p>If you wish to use multiple contexts (even for the same solver), create one SolverContext per
 * each. Formulas can be transferred between different contexts using {@link
 * FormulaManager#translateFrom(BooleanFormula, FormulaManager)}.
 */
public interface SolverContext extends AutoCloseable {

  /** Get the formula manager, which is used for formula manipulation. */
  FormulaManager getFormulaManager();

  /** Options for the prover environment. */
  enum ProverOptions {

    /**
     * Whether the solver should generate models (i.e., satisfying assignments) for satisfiable
     * formulas.
     */
    GENERATE_MODELS,

    /**
     * Whether the solver should allow to query all satisfying assignments for satisfiable formulas.
     */
    GENERATE_ALL_SAT,

    /**
     * Whether the solver should generate an unsat core for unsatisfiable formulas. Unsat core is
     * generated over all formulas asserted with {@link
     * ProverEnvironment#addConstraint(BooleanFormula)} or {@link
     * ProverEnvironment#push(BooleanFormula)}.
     */
    GENERATE_UNSAT_CORE,

    /**
     * Whether the solver should generate an unsat core for unsatisfiable formulas <b>only</b> over
     * the assumptions explicitly passed to the solver.
     */
    GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS,

    /** Whether the solver should enable support for formulae build in SL theory. */
    ENABLE_SEPARATION_LOGIC,

    /**
     * Enables Craig interpolation, using the model-based interpolation strategy. This strategy
     * constructs interpolants based on the model provided by a solver, i.e. model generation must
     * be enabled. This interpolation strategy is only usable for solvers supporting quantified
     * solving over the theories interpolated upon. The solver does not need to support
     * interpolation itself.
     */
    GENERATE_PROJECTION_BASED_INTERPOLANTS,

    /**
     * Enables (uniform) Craig interpolation, using the quantifier-based interpolation strategy
     * utilizing quantifier-elimination in the forward direction. Forward means, that the set of
     * formulas A, used to interpolate, interpolates towards the set of formulas B (B == all
     * formulas that are currently asserted, but not in the given set of formulas A used to
     * interpolate). This interpolation strategy is only usable for solvers supporting
     * quantifier-elimination over the theories interpolated upon. The solver does not need to
     * support interpolation itself.
     */
    GENERATE_UNIFORM_FORWARD_INTERPOLANTS,

    /**
     * Enables (uniform) Craig interpolation, using the quantifier-based interpolation strategy
     * utilizing quantifier-elimination in the backward direction. Backward means, that the set of
     * formulas B (B == all formulas that are currently asserted, but not in the given set of
     * formulas A used to interpolate) interpolates towards the set of formulas A. This
     * interpolation strategy is only usable for solvers supporting quantifier-elimination over the
     * theories interpolated upon. The solver does not need to support interpolation itself.
     */
    GENERATE_UNIFORM_BACKWARD_INTERPOLANTS
  }

  /**
   * Create a fresh new {@link ProverEnvironment} which encapsulates an assertion stack and can be
   * used to check formulas for unsatisfiability.
   *
   * @param options Options specified for the prover environment. All the options specified in
   *     {@link ProverOptions} are turned off by default.
   */
  ProverEnvironment newProverEnvironment(ProverOptions... options);

  /**
   * Create a fresh new {@link InterpolatingProverEnvironment} which encapsulates an assertion stack
   * and allows generating and retrieve interpolants for unsatisfiable formulas. If the SMT solver
   * InterpolatingProverEnvironment} interface, and return an Object of this type here.
   *
   * @param options Options specified for the prover environment. All the options specified in
   *     {@link ProverOptions} are turned off by default.
   */
  InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(ProverOptions... options);

  /**
   * Create a fresh new {@link OptimizationProverEnvironment} which encapsulates an assertion stack
   * and allows solving optimization queries.
   *
   * @param options Options specified for the prover environment. All the options specified in
   *     {@link ProverOptions} are turned off by default.
   */
  OptimizationProverEnvironment newOptimizationProverEnvironment(ProverOptions... options);

  /**
   * Get version information out of the solver.
   *
   * <p>In most cases, the version contains the name of the solver followed by some numbers and
   * additional info about the version, e.g., "SMTInterpol 2.5-12-g3d15a15c".
   */
  String getVersion();

  /**
   * Get solver name (MATHSAT5/Z3/etc...).
   *
   * <p>This is an uppercase String matching the enum identifier from {@link Solvers}
   */
  Solvers getSolverName();

  /**
   * Get statistics for a complete solver context. The returned mapping is intended to provide the
   * solver-internal statistics. The keys can differ between individual solvers.
   *
   * <p>Calling the statistics several times for the same context returns accumulated number, i.e.,
   * we currently do not provide any possibility to reset the statistics.
   *
   * <p>We do not guarantee any specific key to be present, as this depends on the used solver. We
   * might even return an empty mapping if the solver does not support calling this method or is in
   * an invalid state.
   *
   * @see ProverEnvironment#getStatistics()
   */
  default ImmutableMap<String, String> getStatistics() {
    return ImmutableMap.of();
  }

  /**
   * Close the solver context.
   *
   * <p>After calling this method, further access to any object that had been returned from this
   * context is not wanted, i.e., it depends on the solver. Java-based solvers might wait for the
   * next garbage collection with any cleanup operation. Native solvers might even reference invalid
   * memory and cause segmentation faults.
   *
   * <p>Necessary for the solvers implemented in native code, frees the associated memory.
   */
  @Override
  void close();
}
