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
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.api.proofs.visitors.ProofVisitor;

public abstract class AbstractProofNode implements ProofNode {
  private final List<ProofNode> children;
  private ProofRule rule;
  private Formula formula;
  private final UniqueIdGenerator idGenerator = new UniqueIdGenerator();
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

  void setFormula(Formula pFormula) {
    formula = pFormula;
  }
}
