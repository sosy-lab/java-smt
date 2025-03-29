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

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_proof_get_arity;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_proof_get_child;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_proof_get_name;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_proof_get_term;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_proof_is_term;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;
import javax.annotation.Nullable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.proofs.ProofFrame;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProofDag.AbstractProofNode;

public class Mathsat5ProofNode extends AbstractProofNode {

  protected Mathsat5ProofNode(ProofRule rule, Formula formula) {
    super(rule, formula);
  }

  protected static class MsatProofFrame extends ProofFrame<Long> {
    MsatProofFrame(Long proof) {
      super(proof);
    }
  }

  public static Mathsat5ProofNode fromMsatProof(ProverEnvironment pProver, long rootProof) {
    final Mathsat5SolverContext context = ((Mathsat5TheoremProver) pProver).context;
    final long curEnv = ((Mathsat5TheoremProver) pProver).curEnv;
    final Mathsat5FormulaCreator formulaCreator = ((Mathsat5TheoremProver) pProver).creator;

    {
      Deque<MsatProofFrame> stack = new ArrayDeque<>();
      Map<Long, Mathsat5ProofNode> computed = new HashMap<>();

      stack.push(new MsatProofFrame(rootProof));

      while (!stack.isEmpty()) {
        MsatProofFrame frame = stack.peek();

        if (!frame.isVisited()) {
          frame.setNumArgs(msat_proof_get_arity(frame.getProof()));
          frame.setAsVisited(true);
          // Push children first so that the leaves are processed first.
          for (int i = 0; i < frame.getNumArgs(); i++) {
            long child = msat_proof_get_child(frame.getProof(), i);
            if (!computed.containsKey(child)) {
              stack.push(new MsatProofFrame(child));
            }
          }
        } else {
          // Process the node after all its children have been processed. This should help to
          // recreate the formula for the node correctly.
          stack.pop();

          // Generate the formula and proof rule.
          Formula formula = generateFormula(frame.getProof(), (Mathsat5TheoremProver) pProver);
          Mathsat5ProofRule proofRule =
              new Mathsat5ProofRule(msat_proof_get_name(frame.getProof()));
          Mathsat5ProofNode node = new Mathsat5ProofNode(proofRule, formula);

          // Retrieve computed child nodes and attach them.
          for (int i = 0; i < frame.getNumArgs(); i++) {
            long child = msat_proof_get_child(frame.getProof(), i);
            Mathsat5ProofNode childNode = computed.get(child);
            if (childNode != null) {
              node.addChild(childNode);
            }
          }
          computed.put(frame.getProof(), node);
        }
      }
      return computed.get(rootProof);
    }
  }

  @Nullable
  private static Formula generateFormula(long proof, Mathsat5TheoremProver prover) {
    Mathsat5FormulaCreator formulaCreator = prover.creator;
    Formula formula = null;
    if (msat_proof_is_term(proof)) {
      long proofTerm = msat_proof_get_term(proof);
      formula = formulaCreator.encapsulate(formulaCreator.getFormulaType(proofTerm), proofTerm);
    }
    return formula;
  }

  String asString() {
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
