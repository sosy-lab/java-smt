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
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProof;

public class CVC5Proof extends AbstractProof {

  CVC5Subproof generateProofImpl(Proof pProof, CVC5FormulaCreator formulaCreator)
      throws CVC5ApiException {

    // boolean skippedScope = false;

    Deque<CVC5Frame> stack = new ArrayDeque<>();

    Map<Proof, CVC5Subproof> computed = new HashMap<>();

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
        CVC5Subproof pn = new CVC5Subproof(proofRule, pFormula, this);
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

  private static class CVC5Frame extends ProofFrame<Proof> {
    CVC5Frame(Proof proof) {
      super(proof);
    }
  }

  public static class CVC5Subproof extends AbstractSubproof {

    public CVC5Subproof(ProofRule pProofRule, Formula formula, AbstractProof proof) {

      super(pProofRule, formula, proof);
    }

    @Override
    protected void addChild(Subproof pSubproof) {
      super.addChild(pSubproof);
    }

    // private static Proof changeRoot(Proof root) {
    //  return root.getArguments()[0];
    //    }

    @Override
    public String proofAsString() {
      return super.proofAsString();
    }
  }
}
