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

public interface ProofDAG {
  void addNode(ProofNode node);
  ProofNode getNode(int nodeId);
  void addEdge(int parentNodeId, int childNodeId);
  Collection<ProofNode> getNodes();
  void accept(ProofVisitor visitor); // To allow traversal of the entire DAG
}
