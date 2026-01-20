/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.cvc5;

import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Term;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.Proof;
import org.sosy_lab.java_smt.api.proofs.ProofFrame;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

public class CVC5Proof extends org.sosy_lab.java_smt.basicimpl.AbstractProof {

  static CVC5Proof generateProofImpl(io.github.cvc5.Proof pProof, CVC5FormulaCreator formulaCreator)
      throws CVC5ApiException {

    // boolean skippedScope = false;

    Deque<CVC5Frame> stack = new ArrayDeque<>();

    Map<io.github.cvc5.Proof, CVC5Proof> computed = new HashMap<>();

    stack.push(new CVC5Frame(pProof));

    while (!stack.isEmpty()) {
      CVC5Frame frame = stack.peek();

      if (!frame.isVisited()) {

        frame.setNumArgs(frame.getProof().getChildren().length);
        frame.setAsVisited(true);

        for (int i = frame.getNumArgs() - 1; i >= 0; i--) {
          io.github.cvc5.Proof child = frame.getProof().getChildren()[i];
          if (!computed.containsKey(child)) {
            stack.push(new CVC5Frame(child));
          }
        }
      } else {
        stack.pop();
        int numChildren = frame.getNumArgs();

        // if (frame.getProof().getRule().getValue() == 1 && !skippedScope) {
        // Skip processing the frame if its rule is "SCOPE"
        // This rule seems to just help the processing by CVC5
        //  pProof = changeRoot(frame.getProof());
        // skippedScope = true;
        // continue;
        // }

        CVC5ProofRule proofRule =
            Enum.valueOf(CVC5ProofRule.class, frame.getProof().getRule().toString());
        // ProofRule.fromName(
        // CVC5ProofRule.class, frame.getProof().getRule().toString().toLowerCase());

        // Generate formula
        Term term = frame.getProof().getResult();
        Formula pFormula = formulaCreator.encapsulate(formulaCreator.getFormulaType(term), term);
        CVC5Proof pn = new CVC5Proof(proofRule, pFormula);
        for (int i = 0; i < numChildren; i++) {
          io.github.cvc5.Proof child = frame.getProof().getChildren()[i];

          if (computed.containsKey(child)) {
            pn.addChild(computed.get(child));
          }
        }
        computed.put(frame.getProof(), pn);
      }
    }
    return computed.get(pProof);
  }

  private static class CVC5Frame extends ProofFrame<io.github.cvc5.Proof> {
    CVC5Frame(io.github.cvc5.Proof proof) {
      super(proof);
    }
  }

  public CVC5Proof(ProofRule pProofRule, Formula formula) {

    super(pProofRule, formula);
  }

  @Override
  protected void addChild(Proof pProof) {
    super.addChild(pProof);
  }

  // private static Proof changeRoot(Proof root) {
  //  return root.getArguments()[0];
  //    }

  @Override
  public String proofAsString() {
    return super.proofAsString();
  }
}
