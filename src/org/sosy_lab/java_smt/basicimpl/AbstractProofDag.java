/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.api.proofs.ProofDag;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.visitors.ProofVisitor;

/**
 * A proof DAG in the proof DAG of a proof.
 *
 * @author Gabriel Carpio
 */
public abstract class AbstractProofDag implements ProofDag {
  private final Map<Integer, ProofNode> nodes = new HashMap<>();
  private int nodeIdCounter = 0;

  @Override
  public void addNode(ProofNode node) {
    nodes.put(nodeIdCounter++, node);
  }

  @Override
  public ProofNode getNode(int nodeId) {
    return nodes.get(nodeId);
  }

  @Override
  public void addEdge(int parentNodeId, int childNodeId) {
    ProofNode parent = nodes.get(parentNodeId);
    ProofNode child = nodes.get(childNodeId);
    if (parent != null && child != null) {
      parent.addChild(child);
    }
  }

  @Override
  public Collection<ProofNode> getNodes() {
    return nodes.values();
  }

  @Override
  public void accept(ProofVisitor visitor) {
    visitor.visitDAG(this);
  }
}
