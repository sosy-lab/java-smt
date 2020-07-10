// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

/**
 * Tactic is a generic formula to formula transformation.
 *
 * <p>Depending on whether the chosen solver supports the transformation, at runtime switches
 * between solver-provided implementation and our own generic visitor-based one.
 *
 * <p>Tactics can be applied using {@link org.sosy_lab.java_smt.api.FormulaManager#applyTactic}
 */
public enum Tactic {

  /**
   * Replaces all applications of UFs with fresh variables and adds constraints to enforce the
   * functional consistency. Quantified formulas are not supported.
   */
  ACKERMANNIZATION,

  /** Convert the formula to NNF (negated normal form). */
  NNF,

  /**
   * Convert the formula to CNF (conjunctive normal form), using extra fresh variables to avoid the
   * size explosion. The resulting formula is not <i>equivalent</i> but only <i>equisatisfiable</i>
   * to the original one.
   *
   * <p>NB: currently this tactic does not have a default implementation.
   */
  TSEITIN_CNF,

  /**
   * Perform "best-effort" quantifier elimination: when the bound variable can be "cheaply"
   * eliminated using a pattern-matching approach, eliminate it, and otherwise leave it as-is.
   */
  QE_LIGHT,
}
