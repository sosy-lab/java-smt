/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.smtinterpol;

import io.github.cvc5.Proof;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.solvers.cvc5.CVC5ProofNode;
import org.sosy_lab.java_smt.solvers.cvc5.CVC5ProofRule;

@SuppressWarnings({"unchecked", "rawtypes", "unused", "static-access"})
class SmtInterpolProofNodeCreator {
  private final SmtInterpolFormulaCreator creator;
  private final SmtInterpolTheoremProver prover;

  SmtInterpolProofNodeCreator(
      SmtInterpolFormulaCreator pCreator,
      SmtInterpolTheoremProver pProver) {
    creator = pCreator;
    prover = pProver;

  }
 /*

  ProofNode fromTerm(Term pTerm) {

    Deque<Frame> stack = new ArrayDeque<>();

    Map<Proof, CVC5ProofNode> computed = new HashMap<>();

    stack.push(new Frame(rootProof));

    while (!stack.isEmpty()) {
      Frame frame = stack.peek();

      // Skip processing the frame if its rule is "SCOPE"
      // This rule seems to just help the processing by CVC5
      if (!frame.visited && frame.proof.getRule().getValue() == 1) {
        // Pop the SCOPE frame and push its children onto the stack
        stack.pop();
        frame.numChildren = rootProof.getChildren().length;
        frame.visited = true;

        for (int i = frame.numChildren-1; i >= 0; i--) {
          Proof child = rootProof.getChildren()[i];
          if (!computed.containsKey(child)) {
            stack.push(new Frame(child));
          }
        }
      } else {

        stack.pop();
        int numChildren = frame.numChildren;

        CVC5ProofRule proofRule =
            ProofRule.fromName(CVC5ProofRule.class, frame.proof.getRule().toString());
        CVC5ProofNode pn = new CVC5ProofNode(proofRule, generateFormula(frame.proof));
        for (int i = 0; i < numChildren - 1; i++) {
          Proof child = frame.proof.getChildren()[i];

          if (computed.containsKey(child)) {
            pn.addChild(computed.get(child));
          }
        }
        computed.put(frame.proof, pn);
      }
    }
    return computed.get(rootProof);
  }

  */
}
