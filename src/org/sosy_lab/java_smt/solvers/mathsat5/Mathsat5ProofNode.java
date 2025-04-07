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

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_and;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_or;
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
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5ProofRule.Rule;

public class Mathsat5ProofNode extends AbstractProofNode {

  protected Mathsat5ProofNode(@Nullable ProofRule rule, Formula formula) {
    super(rule, formula);
  }

  protected static class MsatProofFrame extends ProofFrame<Long> {
    MsatProofFrame(Long proof) {
      super(proof);
    }

    boolean skip = false;
  }

  /**
   * Creates a proof node from a MathSAT5 proof object.
   *
   * <p>Not all proof rules are known beforehand, so some are not in the enum. This means that
   * (specifically) the sub-DAG of the theory-lemma rule may contain a sub-proof that does not have
   * either a {@link ProofRule} or a {@link Formula} in a given node.
   *
   * @param pProver The prover environment.
   * @param rootProof The root proof object.
   * @return The proof node.
   */
  public static Mathsat5ProofNode fromMsatProof(ProverEnvironment pProver, long rootProof) {

    Deque<MsatProofFrame> stack = new ArrayDeque<>();
    Map<Long, Mathsat5ProofNode> computed = new HashMap<>();

    stack.push(new MsatProofFrame(rootProof));

    while (!stack.isEmpty()) {
      MsatProofFrame frame = stack.peek();

      if (!frame.isVisited()) {
        frame.setAsVisited(true);
        String rule =
            msat_proof_get_name(frame.getProof()) == null
                ? "null"
                : msat_proof_get_name(frame.getProof());

        // If rule is claus-hyp, all the children get added to the dag in generateFormula
        if (!rule.equals("clause-hyp")) {
          frame.setNumArgs(msat_proof_get_arity(frame.getProof()));
          for (int i = frame.getNumArgs() - 1; i >= 0; i--) {
            long child = msat_proof_get_child(frame.getProof(), i);
            if (!computed.containsKey(child)) {
              // If the rules is theory-lemma and the child is  a term, it gets added to the dag
              // in generateFormula otherwise we push it to the stack to be processed later.
              switch (rule) {
                case "theory-lemma":
                  if (msat_proof_is_term(child)) {
                    frame.setNumArgs(frame.getNumArgs() - 1);
                    System.out.println("theory-lemma rule has " + frame.getNumArgs() + " children");
                  } else {
                    System.out.println("pushing theoryy-lemma non term child " + child);
                    System.out.println("thoryy-lemma rule has " + frame.getNumArgs() + " children");
                    stack.push(new MsatProofFrame(child));
                  }
                  break;
                default:
                  stack.push(new MsatProofFrame(child));
                  break;
              }
            }
          }
        }
      } else {

        stack.pop();

        String rule = msat_proof_get_name(frame.getProof());
        ProofRule proofRule;

        // If the theory-lemma rule includes a last argument that is not a term, it means it has
        // a proof attached to it. Not all rules are known beforehand so they are not in the enum.
        try {
          proofRule = rule == null ? Rule.NULL : Rule.valueOf(rule.toUpperCase().replace("-", "_"));
        } catch (IllegalArgumentException e) {
          proofRule = new Mathsat5ProofRule(rule);
        }

        Mathsat5ProofNode node;
        Mathsat5TheoremProver prover = (Mathsat5TheoremProver) pProver;
        Formula formula = generateFormula(frame, prover, proofRule);

        node = new Mathsat5ProofNode(proofRule, formula);

        // Retrieve computed child nodes and attach them. In this case the subtraction is due to
        // the processing of the theory-lemma rule.

        for (int i = (msat_proof_get_arity(frame.getProof()) - frame.getNumArgs());
            i < msat_proof_get_arity(frame.getProof());
            i++) {

          // AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA
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

  @Nullable
  private static Formula generateFormula(
      MsatProofFrame frame, Mathsat5TheoremProver prover, ProofRule rule) {
    Mathsat5FormulaCreator formulaCreator = prover.creator;
    Formula formula = null;
    long proof = frame.getProof();
    int children = msat_proof_get_arity(proof);
    // If rule is NULL the proof should be a term and we encapsulate directly
    if (rule.equals(Rule.NULL)) {
      formula =
          formulaCreator.encapsulate(
              formulaCreator.getFormulaType(msat_proof_get_term(proof)),
              msat_proof_get_term(proof));
      // For clause-hype, we create the clause using the children
    } else if (rule.equals(Rule.CLAUSE_HYP)) {
      long or = msat_proof_get_term(msat_proof_get_child(proof, 0));
      for (int i = 1; i < children; i++) {
        long child = msat_proof_get_term(msat_proof_get_child(proof, i));
        or = msat_make_or(prover.curEnv, or, child);
      }
      formula = formulaCreator.encapsulate(formulaCreator.getFormulaType(or), or);
    } else if (rule.equals(Rule.RES_CHAIN)) {
      // Generating the formula for the resolution chain should be easier after the whole DAG is
      // built
    } else if (rule.equals(Rule.THEORY_LEMMA)) {
      if (msat_proof_is_term(msat_proof_get_child(proof, 0))) {
        long and = msat_proof_get_term(msat_proof_get_child(proof, 0));
        for (int i = 1; i < children; i++) {
          if (msat_proof_is_term(msat_proof_get_child(proof, i))) {
            long child = msat_proof_get_term(msat_proof_get_child(proof, i));
            and = msat_make_and(prover.curEnv, and, child);
          }
        }
        formula = formulaCreator.encapsulate(formulaCreator.getFormulaType(and), and);
      }
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
