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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofDAG;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.api.proofs.visitors.ProofVisitor;

/**
 * A proof DAG in the proof DAG of a proof.
 *
 * @author Gabriel Carpio
 */
public abstract class AbstractProofDAG implements ProofDAG {
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

  public abstract static class AbstractProofNode implements ProofNode {
    private final List<ProofNode> children;
    private ProofRule rule;
    @Nullable protected Formula formula;
    private static final UniqueIdGenerator idGenerator = new UniqueIdGenerator();
    private final int id;

    protected AbstractProofNode(ProofRule rule, Formula formula) {
      this.rule = rule;
      this.formula = formula;
      children = new ArrayList<>();
      id = idGenerator.getFreshId();
    }

    @Override
    public Formula getFormula() {
      return formula;
    }

    @Override
    public List<ProofNode> getChildren() {
      return Collections.unmodifiableList(children);
    }

    @Override
    public void addChild(ProofNode child) {
      children.add(child);
    }

    @Override
    public ProofRule getRule() {
      return rule;
    }

    @Override
    public boolean isLeaf() {
      return children.isEmpty();
    }

    @Override
    public int getId() {
      return id;
    }

    void setRule(ProofRule rule) {
      this.rule = rule;
    }

    public void setFormula(Formula pFormula) {
      formula = pFormula;
    }
  }
}
