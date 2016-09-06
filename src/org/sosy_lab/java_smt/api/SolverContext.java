/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package org.sosy_lab.java_smt.api;

import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

/**
 * Instances of this interface provide access to an SMT solver.
 * A single SolverContext should be used only from a single thread.
 *
 * <p>If you wish to use multiple contexts (even for the same solver),
 * create one SolverContext per each.
 * Formulas can be transferred between different contexts using
 * {@link FormulaManager#translateFrom(BooleanFormula, FormulaManager)}.
 */
public interface SolverContext extends AutoCloseable {

  /**
   * Get the formula manager, which is used for formula manipulation.
   */
  FormulaManager getFormulaManager();

  /**
   * Options for the prover environment.
   */
  enum ProverOptions {

    /**
     * Whether the solver should generate models (i.e., satisfying assignments)
     * for satisfiable formulas.
     */
    GENERATE_MODELS,

    /**
     * Whether the solver should generate an unsat core
     * for unsatisfiable formulas.
     * Unsat core is generated over all formulas asserted
     * with {@link ProverEnvironment#addConstraint(BooleanFormula)}
     * or {@link ProverEnvironment#push(BooleanFormula)}.
     */
    GENERATE_UNSAT_CORE,

    /**
     * Whether the solver should generate an unsat core
     * for unsatisfiable formulas <b>only</b> over the assumptions
     * explicitly passed to the solver.
     */
    GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS
  }

  /**
   * Create a fresh new {@link ProverEnvironment} which encapsulates an assertion stack
   * and can be used to check formulas for unsatisfiability.
   *
   * @param options Options specified for the prover environment.
   *                All of the options specified in {@link ProverOptions}
   *                are turned off by default.
   */
  ProverEnvironment newProverEnvironment(ProverOptions... options);

  /**
   * Create a fresh new {@link InterpolatingProverEnvironment} which encapsulates an assertion stack
   * and allows to generate and retrieve interpolants for unsatisfiable formulas.
   * If the SMT solver is able to handle satisfiability tests with assumptions please consider
   * implementing the {@link InterpolatingProverEnvironment} interface, and return
   * an Object of this type here.
   */
  InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation();

  /**
   * Create a fresh new {@link OptimizationProverEnvironment} which encapsulates an assertion stack
   * and allows to solve optimization queries.
   */
  OptimizationProverEnvironment newOptimizationProverEnvironment();

  /**
   * Get version information out of the solver.
   */
  String getVersion();

  /**
   * Get solver name (MATHSAT5/Z3/etc...).
   */
  Solvers getSolverName();

  /**
   * Close the solver context.
   *
   * <p>Necessary for the solvers implemented in native code, frees the associated
   * memory.
   */
  @Override
  void close();
}
