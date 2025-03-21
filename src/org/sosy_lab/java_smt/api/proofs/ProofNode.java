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

import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.visitors.ProofVisitor;

/**
 * A proof node in the proof DAG of a proof.
 *
 * @author Gabriel Carpio
 */
public interface ProofNode {

  /** Get the children of the proof node. */
  List<ProofNode> getChildren();

  void addChild(ProofNode child);

  boolean isSource();

  boolean isSink();

  void accept(ProofVisitor visitor);

  /**
   * Get the formula of the proof node.
   *
   * @return The formula of the proof node.
   */
  Formula getFormula();

  /**
   * Get the id of the proof node.
   *
   * @return The id of the proof node.
   */
  int getId();
}
