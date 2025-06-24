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

import java.util.LinkedHashSet;
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

  // protected abstract class Transformation {
  //  protected <TFormulaInfo, TType, TEnv, TFuncDecl, T> Transformation(
  //      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> formulaCreator, T proof) {}

  //    protected abstract Proof generateProof();
  // }

  private final Set<Proof> children = new LinkedHashSet<>();
  private ProofRule rule;
  @Nullable protected Formula formula;

  protected AbstractProof(ProofRule rule, Formula formula) {
    this.rule = rule;
    this.formula = formula;
  }

  // TODO: Use Optional instead of nullable
  @Nullable
  @Override
  public Formula getFormula() {
    return this.formula;
  }

  @Override
  public Set<Proof> getChildren() {
    return this.children;
  }

  protected void addChild(Proof child) {
    this.children.add(child);
  }

  @Override
  public ProofRule getRule() {
    return rule;
  }

  @Override
  public boolean isLeaf() {
    return getChildren().isEmpty();
  }

  // void setRule(ProofRule rule) {
  //  this.rule = rule;
  // }

  public void setFormula(Formula pFormula) {
    formula = pFormula;
  }

  // use this for debugging
  public String proofAsString() {
    return proofAsString(0);
  }

  protected String proofAsString(int indentLevel) {
    StringBuilder sb = new StringBuilder();
    String indent = "  ".repeat(indentLevel);

    Formula f = getFormula();
    String sFormula;
    if (f != null) {
      sFormula = f.toString();
    } else {
      sFormula = "null";
    }

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
}
