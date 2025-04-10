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

public class CVC5ProofProcessor {

  private static class CVC5Frame extends ProofFrame<Proof> {
    CVC5Frame(Proof proof) {
      super(proof);
    }
  }

  private final CVC5FormulaCreator formulaCreator;

  CVC5ProofProcessor(CVC5FormulaCreator creator) {
    formulaCreator = creator;
  }

  CVC5ProofNode fromCVC5Proof(Proof pProof) throws CVC5ApiException {

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
        CVC5ProofNode pn = new CVC5ProofNode(proofRule, generateFormula(frame.getProof()));
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

  private Formula generateFormula(Proof proof) {
    Formula formula = null;
    if (formula == null) {
      Term term = proof.getResult();
      formula = formulaCreator.encapsulate(formulaCreator.getFormulaType(term), term);
    }
    return formula;
  }

  private Proof changeRoot(Proof root) {
    return root.getChildren()[0];
  }
}
