/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.api.proofs;

/**
 * This gives access to the optional parameters in some of the Z3 proof rules.
 *
 * @param <T> the type of the parameter.
 */
public interface Z3ProofRuleParameter<T> {

  /**
   * Get the value of a parameter.
   *
   * @return the value of the parameter.
   */
  T getValue();
}
