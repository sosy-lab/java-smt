/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.collect.ImmutableSet;
import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.Proof;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

/**
 * A proof DAG of a proof.
 *
 * @author Gabriel Carpio
 */
public abstract class AbstractProof implements Proof {

  private ImmutableSet<Proof> children = ImmutableSet.of();
  private ProofRule rule;
  protected Optional<Formula> formula = Optional.empty();

  protected AbstractProof(ProofRule rule, @Nullable Formula formula) {
    this.rule = rule;
    this.formula = Optional.ofNullable(formula);
  }

  @Override
  public Optional<Formula> getFormula() {
    return this.formula;
  }

  @Override
  public ImmutableSet<Proof> getChildren() {
    return this.children;
  }

  protected void addChild(Proof child) {
    Set<Proof> tempChildren = new LinkedHashSet<>(this.children);
    tempChildren.add(child);
    this.children = ImmutableSet.copyOf(tempChildren);
  }

  @Override
  public ProofRule getRule() {
    return rule;
  }

  @Override
  public boolean isLeaf() {
    return getChildren().isEmpty();
  }

  public void setFormula(@Nullable Formula pFormula) {
    formula = Optional.ofNullable(pFormula);
  }

  public void setRule(ProofRule pRule) {
    rule = pRule;
  }

  // use this for debugging
  public String proofAsString() {
    return proofAsString(0);
  }

  protected String proofAsString(int indentLevel) {
    StringBuilder sb = new StringBuilder();
    String indent = "  ".repeat(indentLevel);

    String sFormula = getFormula().map(Object::toString).orElse("null");

    sb.append(indent).append("Formula: ").append(sFormula).append("\n");
    sb.append(indent).append("Rule: ").append(getRule().getName()).append("\n");
    sb.append(indent)
        .append("No. Children: ")
        .append(this.isLeaf() ? 0 : getChildren().size())
        .append("\n");
    sb.append(indent).append("leaf: ").append(isLeaf()).append("\n");

    int i = 0;
    if (!isLeaf()) {
      for (Proof child : getChildren()) {
        sb.append(indent).append("Child ").append(++i).append(":\n");
        sb.append(((AbstractProof) child).proofAsString(indentLevel + 1));
      }
    }

    return sb.toString();
  }

  protected abstract static class ProofFrame<T> {
    final T proof;
    int numArgs = 0;
    boolean visited;

    protected ProofFrame(T proof) {
      this.proof = proof;
      this.visited = false;
    }

    /** Get the proof object. */
    public T getProof() {
      return proof;
    }

    /** Get the number of arguments the proof object has. */
    public int getNumArgs() {
      return numArgs;
    }

    /** Check if the frame has been visited. */
    public boolean isVisited() {
      return visited;
    }

    /** Set the frame as visited. */
    public void setAsVisited(boolean isVisited) {
      this.visited = isVisited;
    }

    /** Set the number of arguments the proof object has. */
    public void setNumArgs(int numArgs) {
      this.numArgs = numArgs;
    }
  }
}
