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
import org.sosy_lab.java_smt.ResProofRule.ResAxiom;
import org.sosy_lab.java_smt.api.proofs.ProofDAG;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.visitors.ProofVisitor;

/**
 * A proof DAG in the proof DAG of a proof.
 *
 * @author Gabriel Carpio
 */
public abstract class AbstractProofDAG<R> implements ProofDAG<R> {
  private final Map<Integer, ProofNode<R>> nodes = new HashMap<>();
  private int nodeIdCounter = 0;

  @Override
  public void addNode(ProofNode<R> node) {
    nodes.put(nodeIdCounter++, node);
  }

  @Override
  public ProofNode<R> getNode(int nodeId) {
    return nodes.get(nodeId);
  }

  @Override
  public void addEdge(ProofNode<R> parentNodeId, ProofNode<R> childNodeId) {
    ProofNode<R> parent = nodes.get(parentNodeId);
    ProofNode<R> child = nodes.get(childNodeId);
    if (parent != null && child != null) {
      parent.addChild(child);
    }
  }

  @Override
  public Collection<ProofNode<R>> getNodes() {
    return nodes.values();
  }

  @Override
  public void accept(ProofVisitor<R> visitor) {
    visitor.visitDAG(this);
  }
}