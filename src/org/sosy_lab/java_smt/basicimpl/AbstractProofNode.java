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
import java.util.Collections;
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.visitors.ProofVisitor;

/**
 * A proof node in the proof DAG of a proof.
 *
 * @author Gabriel Carpio
 */
public abstract class AbstractProofNode<R> implements ProofNode<R> {
  private final List<ProofNode<R>> children;
  private final R rule;
  private final Formula formula;

  protected AbstractProofNode(R rule, Formula formula) {
    this.rule = rule;
    this.formula = formula;
    children = new ArrayList<>();
  }

  @Override
  public Formula getFormula() {
    return formula;
  }

  @Override
  public List<ProofNode<R>> getChildren() {
    return Collections.unmodifiableList(children);
  }

  @Override
  public void addChild(ProofNode<R> child) {
    children.add(child);
  }

  public R getRule() {
    return rule;
  }

  @Override
  public boolean isSource() {
    return false;
  }

  @Override
  public boolean isSink() {
    return children.isEmpty();
  }

  @Override
  public void accept(ProofVisitor<R> visitor) {
    visitor.visitNode(this);
  }
}