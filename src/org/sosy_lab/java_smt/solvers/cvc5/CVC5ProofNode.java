/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.cvc5;

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProofDAG.AbstractProofNode;

public class CVC5ProofNode extends AbstractProofNode {

  public CVC5ProofNode(ProofRule pProofRule, Formula formula) {

    super(pProofRule, formula);
  }

  String asString(int indentLevel) {
    StringBuilder proof = new StringBuilder();
    String indent = "  ".repeat(indentLevel);

    proof.append(indent).append("Formula: ").append(getFormula().toString()).append("\n");
    proof.append(indent).append("Rule: ").append(getRule().getName()).append("\n");
    proof.append(indent).append("No. Children: ").append(getChildren().size()).append("\n");
    proof.append(indent).append("ID: ").append(getId()).append("\n");
    proof.append(indent).append("leaf: ").append(isLeaf()).append("\n");

    int i = 0;
    for (ProofNode child : getChildren()) {
      proof.append(indent).append("Child ").append(++i).append(":\n");
      proof.append(((CVC5ProofNode) child).asString(indentLevel + 1));
    }

    return proof.toString();
  }
}
