/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3;

import com.microsoft.z3.Native;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import com.microsoft.z3.enumerations.Z3_sort_kind;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofFrame;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProofDAG;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class Z3ProofDAG extends AbstractProofDAG {
  protected static class Frame extends ProofFrame<Long> {
    protected Frame(Long proof) {
      super(proof);
    }
  }

  public static class Z3ProofNode extends AbstractProofNode {

    Z3ProofNode(Formula pFormula, ProofRule pProofRule) {
      super(pProofRule, pFormula);
    }

    /**
     * This transformation omits one level of the proofs from Z3, as the leaves in that case are the
     * operands of the boolean formulas used as the very first proof steps in the whole proof .E.g.,
     * when asserting (or (not q2) q1) that produces a single {@link Z3ProofNode}, but the input for
     * that is a whole subtree from Z3 composed of the asseertion, the OR operation and the
     * operands.
     *
     * @param rootProof
     * @param formulaCreator
     * @return
     */
    static Z3ProofNode fromZ3Proof(long rootProof, FormulaCreator formulaCreator) {
      long z3context = (long) formulaCreator.getEnv();
      // proof ast to be processed wrapped inside a frame
      Deque<Frame> stack = new ArrayDeque<>();

      // proof ast has been converted into ProofNode
      Map<Long, Z3ProofNode> computed = new HashMap<>();

      stack.push(new Frame(rootProof));

      while (!stack.isEmpty()) {
        Frame frame = stack.peek();

        // prevent processing the same proof ast multiple times
        if (!frame.isVisited()) {

          Native.incRef(z3context, frame.getProof());

          // The number of children of the proof node
          frame.setNumArgs(Native.getAppNumArgs(z3context, frame.getProof()));
          frame.setAsVisited(true);

          for (int i = frame.getNumArgs() - 2; i >= 0; i--) {
            long arg = Native.getAppArg(z3context, frame.getProof(), i);

            if (!computed.containsKey(arg)) {
              stack.push(new Frame(arg));
            }
          }
        } else {

          stack.pop();
          int numArgs = frame.getNumArgs();
          Formula formula;

          // needed for the sortKind
          long sort = Native.getSort(z3context, frame.getProof());
          long sortKind = Native.getSortKind(z3context, sort);
          Z3_sort_kind sk = Z3_sort_kind.fromInt((int) sortKind);
          if (sk != Z3_sort_kind.Z3_UNKNOWN_SORT) {
            // This should be a proof sort, this is not included in the enum class provided by the
            // API
            formula =
                formulaCreator.encapsulate(
                    formulaCreator.getFormulaType(frame.getProof()), frame.getProof());
          } else {
            // Return the i-th argument of the given application. The formula resulting from
            // applying the proof rule is the last argument of the proof node.
            long z3expr = Native.getAppArg(z3context, frame.getProof(), numArgs - 1);
            formula = formulaCreator.encapsulate(formulaCreator.getFormulaType(z3expr), z3expr);
          }
          int declKind =
              Native.getDeclKind(z3context, Native.getAppDecl(z3context, frame.getProof()));
          ProofRule proofRule = getPRfromDK(declKind);
          Z3ProofDAG.Z3ProofNode node = new Z3ProofDAG.Z3ProofNode(formula, proofRule);

          for (int i = 0; i < numArgs - 1; i++) {
            long arg = Native.getAppArg(z3context, frame.getProof(), i);
            if (computed.containsKey(arg)) {
              node.addChild(computed.get(arg));
            }
          }
          computed.put(frame.getProof(), node);
          Native.decRef(z3context, frame.getProof());
        }
      }
      return computed.get(rootProof);
    }

    private static ProofRule getPRfromDK(int declKind) {
      String rawName = Z3_decl_kind.fromInt(declKind).name();
      String prName = rawName.replaceFirst("Z3_OP_PR_", "");
      // return ProofRule.fromName(Z3ProofRule.class, prName);
      return Enum.valueOf(Z3ProofRule.class, prName);
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
      proof.append(indent).append("ID: ").append(getId()).append("\n");
      proof.append(indent).append("leaf: ").append(isLeaf()).append("\n");

      int i = 0;
      for (ProofNode child : getChildren()) {
        proof.append(indent).append("Child ").append(++i).append(":\n");
        proof.append(((Z3ProofNode) child).asString(indentLevel + 1));
      }

      return proof.toString();
    }
  }
}
