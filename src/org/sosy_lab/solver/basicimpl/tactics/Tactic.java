/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.basicimpl.tactics;

/**
 * Tactic is a generic formula to formula transformation.
 *
 * <p>Depending on whether the chosen solver supports the transformation,
 * at runtime switches between solver-provided implementation and our own generic
 * visitor-based one.
 *
 * <p>Tactics can be applied using {@link org.sosy_lab.solver.api.FormulaManager#applyTactic}
 */
public enum Tactic {

  /**
   * Convert the formula to NNF (negated normal form).
   */
  NNF,

  /**
   * Convert the formula to CNF (conjunctive normal form), using extra fresh variables
   * to avoid the size explosion.
   *
   * <p>NB: currently this tactic does not have default implementation.
   */
  CNF,

  /**
   * Perform "best-effort" quantifier elimination:
   * when the bound variable can be "cheaply" eliminated using a pattern-matching
   * approach, eliminate it, and otherwise leave it as-is.
   */
  QE_LIGHT,
}
