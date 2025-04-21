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

import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Proof;
import io.github.cvc5.Term;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofFrame;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProofDAG;



public class CVC5ProofDAG extends AbstractProofDAG {
  private static class CVC5Frame extends ProofFrame<Proof> {
    CVC5Frame(Proof proof) {
      super(proof);
    }
  }
  public static class CVC5ProofNode extends AbstractProofNode {

    public CVC5ProofNode(ProofRule pProofRule, Formula formula) {

      super(pProofRule, formula);
    }

    static CVC5ProofNode fromCVC5Proof(Proof pProof, CVC5FormulaCreator formulaCreator) throws CVC5ApiException {

      boolean skippedScope = false;

      Deque<CVC5Frame> stack = new ArrayDeque<>();

      Map<Proof, CVC5ProofNode> computed = new HashMap<>();

      stack.push(new CVC5Frame(pProof));

      while (!stack.isEmpty()) {
        CVC5Frame frame = stack.peek();

        if (!frame.isVisited()) {

          frame.setNumArgs(frame.getProof().getChildren().length);
          frame.setAsVisited(true);

          for (int i = frame.getNumArgs() - 1; i >= 0; i--) {
            Proof child = frame.getProof().getChildren()[i];
            if (!computed.containsKey(child)) {
              stack.push(new CVC5Frame(child));
            }
          }
        } else {
          stack.pop();
          int numChildren = frame.getNumArgs();

          if (frame.getProof().getRule().getValue() == 1 && !skippedScope) {
            // Skip processing the frame if its rule is "SCOPE"
            // This rule seems to just help the processing by CVC5
            pProof = changeRoot(frame.getProof());
            skippedScope = true;
            continue;
          }

          CVC5ProofRule proofRule =
              Enum.valueOf(CVC5ProofRule.class, frame.getProof().getRule().toString());
          // ProofRule.fromName(
          // CVC5ProofRule.class, frame.getProof().getRule().toString().toLowerCase());

          //Generate formula
          Term term = frame.getProof().getResult();
          Formula pFormula = formulaCreator.encapsulate(formulaCreator.getFormulaType(term), term);
          CVC5ProofNode pn = new CVC5ProofNode(proofRule, pFormula);
          for (int i = 0; i < numChildren; i++) {
            Proof child = frame.getProof().getChildren()[i];

            if (computed.containsKey(child)) {
              pn.addChild(computed.get(child));
            }
          }
          computed.put(frame.getProof(), pn);
        }
      }
      return computed.get(pProof);
    }

    private static Proof changeRoot(Proof root) {
      return root.getChildren()[0];
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
}
