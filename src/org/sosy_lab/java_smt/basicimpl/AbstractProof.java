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

import com.google.common.base.Preconditions;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
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

  protected final Map<Subproof, LinkedHashSet<Subproof>> edges = new HashMap<>();

  protected void addEdge(Subproof source, Subproof target) {
    Preconditions.checkNotNull(source);
    Preconditions.checkNotNull(target);
    edges.putIfAbsent(source, new LinkedHashSet<>());
    edges.get(source).add(target);
  }

  @Override
  public Collection<Subproof> getSubproofs() {
    return edges.keySet();
  }

  public abstract static class AbstractSubproof implements Subproof {
    private final AbstractProof proof;
    private ProofRule rule;
    @Nullable protected Formula formula;

    protected AbstractSubproof(ProofRule rule, Formula formula, AbstractProof proof) {
      this.rule = rule;
      this.formula = formula;
      this.proof = proof;
    }

    @Override
    public Formula getFormula() {
      return formula;
    }

    @Override
    public LinkedHashSet<Subproof> getArguments() {
      return this.proof.edges.get(this);
    }

    protected void addChild(Subproof child) {
      this.proof.addEdge(this, child);
    }

    @Override
    public ProofRule getRule() {
      return rule;
    }

    @Override
    public boolean isLeaf() {
      return getArguments() == null;
    }

    // void setRule(ProofRule rule) {
    //  this.rule = rule;
    // }

    public void setFormula(Formula pFormula) {
      formula = pFormula;
    }

    public Proof getDAG() {
      return proof;
    }

    // use this for debugging
    public String proofAsString() {
      return proofAsString(0);
    }

    protected String proofAsString(int indentLevel) {
      StringBuilder proof = new StringBuilder();
      String indent = "  ".repeat(indentLevel);

      Formula formula = getFormula();
      String sFormula;
      if (formula != null) {
        sFormula = formula.toString();
      } else {
        sFormula = "null";
      }

      proof.append(indent).append("Formula: ").append(sFormula).append("\n");
      proof.append(indent).append("Rule: ").append(getRule().getName()).append("\n");
      proof
          .append(indent)
          .append("No. Children: ")
          .append(this.isLeaf() ? 0 : getArguments().size())
          .append("\n");
      proof.append(indent).append("leaf: ").append(isLeaf()).append("\n");

      int i = 0;
      if (!isLeaf()) {
        for (Subproof child : getArguments()) {
          proof.append(indent).append("Child ").append(++i).append(":\n");
          proof.append(((AbstractSubproof) child).proofAsString(indentLevel + 1));
        }
      }

      return proof.toString();
    }
  }
}
