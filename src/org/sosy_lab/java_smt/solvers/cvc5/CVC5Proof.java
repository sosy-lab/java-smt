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

import com.google.common.collect.ImmutableMap;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Term;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.Map;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.Proof;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

/** A proof of unsatisfiability returned by CVC5 transformed to the general proof API. */
public final class CVC5Proof extends org.sosy_lab.java_smt.basicimpl.AbstractProof {

  static CVC5Proof generateProofImpl(
      io.github.cvc5.Proof pProof, CVC5FormulaCreator pFormulaCreator) throws CVC5ApiException {

    Deque<CVC5Frame> stack = new ArrayDeque<>();
    Map<io.github.cvc5.Proof, CVC5Proof> tempComputed;

    ImmutableMap<io.github.cvc5.Proof, CVC5Proof> computed = ImmutableMap.of();

    stack.push(new CVC5Frame(pProof));

    while (!stack.isEmpty()) {
      CVC5Frame frame = stack.peek();

      if (!frame.isVisited()) {

        frame.setNumArgs(frame.getProof().getChildren().length);
        frame.setAsVisited();

        for (int i = frame.getNumArgs() - 1; i >= 0; i--) {
          io.github.cvc5.Proof child = frame.getProof().getChildren()[i];
          if (!computed.containsKey(child)) {
            stack.push(new CVC5Frame(child));
          }
        }
      } else {
        stack.pop();
        int numChildren = frame.getNumArgs();

        CVC5ProofRule proofRule =
            Enum.valueOf(CVC5ProofRule.class, frame.getProof().getRule().toString());

        // Generate formula
        Term term = frame.getProof().getResult();
        Formula pFormula = pFormulaCreator.encapsulate(pFormulaCreator.getFormulaType(term), term);
        CVC5Proof pn = new CVC5Proof(proofRule, pFormula);
        for (int i = 0; i < numChildren; i++) {
          io.github.cvc5.Proof child = frame.getProof().getChildren()[i];

          if (computed.containsKey(child)) {
            pn.addChild(computed.get(child));
          }
        }
        tempComputed = new LinkedHashMap<>(computed);
        tempComputed.put(frame.getProof(), pn);
        computed = ImmutableMap.copyOf(tempComputed);
      }
    }
    return computed.get(pProof);
  }

  private static class CVC5Frame extends ProofFrame<io.github.cvc5.Proof> {
    CVC5Frame(io.github.cvc5.Proof proof) {
      super(proof);
    }
  }

  private CVC5Proof(ProofRule pProofRule, Formula pFormula) {

    super(pProofRule, pFormula);
  }

  @Override
  protected void addChild(Proof pChild) {
    super.addChild(pChild);
  }

  @Override
  public String proofAsString() {
    return super.proofAsString();
  }
}
