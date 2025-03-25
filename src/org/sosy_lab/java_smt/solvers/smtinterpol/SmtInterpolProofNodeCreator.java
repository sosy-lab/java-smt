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

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import io.github.cvc5.Proof;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.api.proofs.ProofFrame;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

// SMTInterpol gives back a Term (apparently) only of instance ApplicationTerm or AnnotatedTerm,
// so the other instances are not needed.

@SuppressWarnings({"unchecked", "rawtypes", "unused", "static-access"})
class SmtInterpolProofNodeCreator {
  private final SmtInterpolFormulaCreator creator;
  private final SmtInterpolTheoremProver prover;

  SmtInterpolProofNodeCreator(
      SmtInterpolFormulaCreator pCreator, SmtInterpolTheoremProver pProver) {
    creator = pCreator;
    prover = pProver;
  }

  private class SmtTermFrame extends ProofFrame<Term> {
    public SmtTermFrame(Term term) {
      super(term);
    }
  }

  ProofNode fromTerm(Term rootProof) {

    Deque<SmtTermFrame> stack = new ArrayDeque<>();

    Map<Proof, ProofNode> computed = new HashMap<>();

    stack.push(new SmtTermFrame(rootProof));

    while (!stack.isEmpty()) {
      SmtTermFrame frame = stack.peek();

      // Skip processing the frame if its rule is "SCOPE"
      // This rule seems to just help the processing by CVC5
      if (!frame.isVisited() && frame.getProof() == null) {
        // Pop the SCOPE frame and push its children onto the stack
        stack.pop();
        // frame.setNumArgs(rootProof.
        frame.setAsVisited(true);
        // numChildren - 1 iterations
        for (int i = 10 - 1; i >= 0; i--) {
          // Proof child = rootProof.getChildren()[i];
          // !Computed.containsKey(child)
          if (true) {
            // stack.push(new Frame(child));
          }
        }
      } else {

        stack.pop();
        int numChildren = frame.getNumArgs();

        // ProofRule proofRule =
        // new source node or resolution node
        for (int i = 0; i < numChildren - 1; i++) {
          // Proof child = frame.getProof().getChildren()[i];

          // if (computed.containsKey(child)) {
          if (true) {
            // pn.addChild(computed.get(child));
          }
        }
        // computed.put(frame.proof, pn);
      }
    }
    return computed.get(rootProof);
  }

  private class ProvitionalProofNode {
    private Term pivot;
    private ProofRule proofRule;
    private Term formula;
    private int numChildren;

    public ProvitionalProofNode() {}

    public void setFormula(Term pFormula) {
      formula = pFormula;
    }

    public void setPivot(Term pPivot) {
      pivot = pPivot;
    }

    public void setProofRule(ProofRule pProofRule) {
      proofRule = pProofRule;
    }

    public void setNumChildren(int pNumChildren) {
      numChildren = pNumChildren;
    }

    public Term getFormula() {
      return formula;
    }

    public Term getPivot() {
      return pivot;
    }

    public ProofRule getProofRule() {
      return proofRule;
    }

    public int getNumChildren() {
      return numChildren;
    }

    void processAnnotated(AnnotatedTerm term) {
      for (Annotation annotation : term.getAnnotations()) {
        String key = annotation.getKey().substring(1);
        if (annotation.getKey().equals("proves")) {
          this.setFormula((Term) annotation.getValue());
        }

        switch (annotation.getKey()) {
          case ":proves":
            this.setFormula((Term) annotation.getValue());
            break;
          case ":rup":
            this.setFormula((Term) annotation.getValue());
            break;
          case ":input":
            this.setFormula((Term) annotation.getValue());
            break;
          default:
            break;
        }
      }
    }
  }
}
