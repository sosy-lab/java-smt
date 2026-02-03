/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.api.proofs;

import com.google.common.collect.ImmutableSet;
import java.util.Optional;
import org.sosy_lab.java_smt.api.Formula;

/** A proof node in the proof DAG of a proof. */
public interface ProofNode {

  /** Get the children of the proof node. */
  ImmutableSet<ProofNode> getChildren();

  /**
   * Check if the proof node is a leaf.
   *
   * @return True if the proof node is a leaf, false otherwise.
   */
  boolean isLeaf();

  /**
   * Get the formula of the proof node.
   *
   * @return The formula of the proof node.
   */
  Optional<Formula> getFormula();

  /**
   * Get the rule of the proof node.
   *
   * @return The rule of the proof node.
   */
  ProofRule getRule();
}
