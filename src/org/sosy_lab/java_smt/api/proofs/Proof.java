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

import java.util.Set;
import org.sosy_lab.java_smt.api.Formula;

/**
 * A proof node in the proof DAG of a proof.
 *
 * @author Gabriel Carpio
 */
public interface Proof {

  /** Get the children of the proof node. */
  Set<Proof> getChildren();

  boolean isLeaf();

  /**
   * Get the formula of the proof node.
   *
   * @return The formula of the proof node.
   */
  Formula getFormula();

  ProofRule getRule();
}
