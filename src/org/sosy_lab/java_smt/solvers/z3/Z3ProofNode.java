package org.sosy_lab.java_smt.solvers.z3;

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProofNode;

class Z3ProofNode extends AbstractProofNode {

  Z3ProofNode(Formula pFormula, ProofRule pProofRule) {
    super(pProofRule, pFormula);
  }

  String asString() {
    return asString(0);
  }

  private String asString(int indentLevel) {
    StringBuilder proof = new StringBuilder();
    String indent = "  ".repeat(indentLevel);

    proof.append(indent).append("Formula: ").append(getFormula().toString()).append("\n");
    proof.append(indent).append("Rule: ").append(getRule().getName()).append("\n");
    proof.append(indent).append("No. Children: ").append(getChildren().size()).append("\n");

    int i = 0;
    for (ProofNode child : getChildren()) {
      proof.append(indent).append("Child ").append(++i).append(":\n");
      proof.append(((Z3ProofNode) child).asString(indentLevel + 1));
    }

    return proof.toString();
  }

}