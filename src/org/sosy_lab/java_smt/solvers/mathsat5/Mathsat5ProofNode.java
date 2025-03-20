/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.mathsat5;

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProofNode;

public class Mathsat5ProofNode extends AbstractProofNode {

  protected Mathsat5ProofNode(
      ProofRule rule,
      Formula formula) {
    super(rule, formula);
  }

  public String asString() {
    return asString(0);
  }

  private String asString(int indentLevel) {
    StringBuilder proof = new StringBuilder();
    String indent = "  ".repeat(indentLevel);
    if (getFormula() != null) {
      proof.append(indent).append("Formula: ").append(getFormula().toString()).append("\n");
    }
    proof.append(indent).append("Rule: ").append(getRule().getName()).append("\n");
    proof.append(indent).append("No. Children: ").append(getChildren().size()).append("\n");

    int i = 0;
    for (ProofNode child : getChildren()) {
      proof.append(indent).append("Child ").append(++i).append(":\n");
      proof.append(((Mathsat5ProofNode) child).asString(indentLevel + 1));
    }
    return proof.toString();
  }
}
