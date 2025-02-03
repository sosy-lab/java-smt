/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt;

import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.basicimpl.AbstractProofDAG;

public class ResolutionProofDAG<R> extends AbstractProofDAG<R> {

  @Override
  public void addNode(ProofNode<R> node) {
    super.addNode(node);
  }

  @Override
  public ProofNode<R> getNode(int nodeId) {
    return super.getNode(nodeId);
  }

  @Override
  public void addEdge(int parentNodeId, int childNodeId) {
    super.addEdge(parentNodeId, childNodeId);
  }
}
