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

public class Mathsat5ProofProcessor {
  private final Mathsat5SolverContext context;
  private final long curEnv;
  private final Mathsat5FormulaCreator formulaCreator;
  private final Mathsat5TheoremProver theoremProver;

  Mathsat5ProofProcessor(
      Mathsat5SolverContext ctx, long pCurEnv, Mathsat5FormulaCreator creator,
      Mathsat5TheoremProver prover) {
    context = ctx;
    curEnv = pCurEnv;
    formulaCreator = creator;
    theoremProver = prover;
  }

  public Mathsat5ProofNode fromMsatProof(long rootProof) {
    Deque<Frame> stack = new ArrayDeque<>();
    Map<Long, Mathsat5ProofNode> computed = new HashMap<>();

    stack.push(new Frame(rootProof));

    while (!stack.isEmpty()) {
      Frame frame = stack.peek();

      if (!frame.visited) {
        frame.numArgs = msat_proof_get_arity(frame.proof);
        frame.visited = true;
        // Push children first so that the leaves are processed first.
        for (int i = 0; i < frame.numArgs; i++) {
          long child = msat_proof_get_child(frame.proof, i);
          if (!computed.containsKey(child)) {
            stack.push(new Frame(child));
          }
        }
      } else {
        // Process the node after all its children have been processed. This should help to
        // recreate the formula for the node correctly.
        stack.pop();

        // Generate the formula and proof rule.
        Formula formula = generateFormula(frame.proof);
        Mathsat5ProofRule proofRule = new Mathsat5ProofRule(msat_proof_get_name(frame.proof));
        Mathsat5ProofNode node = new Mathsat5ProofNode(proofRule, formula);

        // Retrieve computed child nodes and attach them.
        for (int i = 0; i < frame.numArgs; i++) {
          long child = msat_proof_get_child(frame.proof, i);
          Mathsat5ProofNode childNode = computed.get(child);
          if (childNode != null) {
            node.addChild(childNode);
          }
        }
        computed.put(frame.proof, node);
      }
    }
    return computed.get(rootProof);
  }

  @Nullable
  private Formula generateFormula(long proof) {
    Formula formula = null;
    if (msat_proof_is_term(proof)) {
      long proofTerm = msat_proof_get_term(proof);
      formula = formulaCreator.encapsulate(formulaCreator.getFormulaType(proofTerm), proofTerm);
    }
    return formula;
  }

  private static class Frame {
    final long proof;
    int numArgs;
    boolean visited;

    Frame(long proof) {
      this.proof = proof;
      this.visited = false;
    }
  }
}
