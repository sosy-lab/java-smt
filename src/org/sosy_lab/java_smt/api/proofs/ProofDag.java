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

import java.util.Collection;
import org.sosy_lab.java_smt.api.proofs.visitors.ProofVisitor;

/**
 * A DAG representing a proof. Each node in the DAG is a {@link ProofNode} and each edge is a
 * directed edge from a parent node to a child node.
 */
public interface ProofDag {

  /**
   * Add a node to the DAG.
   *
   * @param node
   */
  void addNode(ProofNode node);

  /**
   * Get a node from the DAG.
   *
   * @param nodeId
   * @return
   */
  ProofNode getNode(int nodeId);

  /**
   * Add an edge to the DAG.
   *
   * @param parentNodeId
   * @param childNodeId
   */
  void addEdge(int parentNodeId, int childNodeId);

  /** Get all nodes in the DAG. */
  Collection<ProofNode> getNodes();

  void accept(ProofVisitor visitor); // To allow traversal of the entire DAG
}
