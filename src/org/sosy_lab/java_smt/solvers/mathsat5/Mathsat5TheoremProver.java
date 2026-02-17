// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5FormulaManager.getMsatTerm;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_assert_formula;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_proof_manager;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_proof;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_proof_manager;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5Proof.fromMsatProof;

import com.google.common.base.Preconditions;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.proofs.Proof;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5ProofRule.Rule;

class Mathsat5TheoremProver extends Mathsat5AbstractProver<Void> implements ProverEnvironment {

  Mathsat5TheoremProver(
      Mathsat5SolverContext pMgr,
      ShutdownNotifier pShutdownNotifier,
      Mathsat5FormulaCreator creator,
      Set<ProverOptions> options) {
    super(pMgr, options, creator, pShutdownNotifier);
  }

  @Override
  protected void createConfig(Map<String, String> pConfig) {
    // nothing to do
  }

  @Override
  @Nullable
  protected Void addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    Preconditions.checkState(!closed);
    closeAllEvaluators();
    msat_assert_formula(curEnv, getMsatTerm(constraint));
    return null;
  }

  @Override
  public Proof getProof() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(this.isUnsat());
    checkGenerateProofs();

    Mathsat5Proof root;
    long pm;
    try {
      pm = msat_get_proof_manager(curEnv);
    } catch (IllegalArgumentException e) {
      throw new UnsupportedOperationException("No proof available.", e);
    }
    long msatProof = msat_get_proof(pm);
    root = fromMsatProof(this, msatProof);
    clausifyResChain(root, context.getFormulaManager().getBooleanFormulaManager());
    msat_destroy_proof_manager(pm);

    return root;

    // return getProof0();
  }

  // update all RES_CHAIN nodes in the proof DAG by computing resolution
  // formulas and return the updated root node with formulas attached.
  private void clausifyResChain(Proof root, BooleanFormulaManager bfmgr) {
    Map<Proof, Boolean> visited = new HashMap<>(); // Track visited nodes
    Deque<Proof> stack = new ArrayDeque<>();

    stack.push(root); // Start with the root node
    visited.put(root, Boolean.FALSE); // Mark root as unvisited

    while (!stack.isEmpty()) {
      Proof node = stack.peek(); // Look at the top node, but don't pop yet

      if (visited.get(node).equals(Boolean.FALSE)) {
        // First time visiting this node
        visited.put(node, Boolean.TRUE); // Mark node as visited

        // Push all children onto stack
        if (!node.isLeaf()) {
          Set<Proof> childrenSet = node.getChildren();
          List<Proof> children = new ArrayList<>(childrenSet);
          for (int i = children.size() - 1; i >= 0; i--) {
            Proof child = children.get(i);
            if (!visited.containsKey(child)) {
              stack.push(child); // Only push unvisited children
              visited.put(child, Boolean.FALSE); // Mark child as unvisited
            }
          }
        }
      } else {
        // All children have been visited, now process the node
        stack.pop(); // Pop the current node as we are done processing its children

        // Check if this node is a RES_CHAIN, process if true
        if (node.getRule().equals(Rule.RES_CHAIN)) {
          processResChain(node, bfmgr); // Process RES_CHAIN node
        }
      }
    }
  }

  // process proof nodes and compute formulas for res-chain nodes
  private void processResChain(Proof node, BooleanFormulaManager bfmgr) {
    Set<Proof> childrenSet = node.getChildren();
    List<Proof> children = new ArrayList<>(childrenSet);

    // If the current node is a RES_CHAIN, compute the resolved formula
    if (node.getRule().equals(Rule.RES_CHAIN)) {
      // Sanity check: res-chain nodes must have an odd number of children (clause, pivot, clause,
      // ..., clause)
      if (children.size() < 3 || children.size() % 2 == 0) {
        throw new IllegalArgumentException("Invalid res-chain structure: must be odd and >= 3");
      }

      // Begin resolution chain: start with the first clause
      BooleanFormula current = (BooleanFormula) children.get(0).getFormula().orElseThrow();

      // Apply resolution iteratively using pivot, clause pairs
      for (int i = 1; i < children.size() - 1; i += 2) {
        BooleanFormula pivot = (BooleanFormula) children.get(i).getFormula().orElseThrow();
        BooleanFormula nextClause = (BooleanFormula) children.get(i + 1).getFormula().orElseThrow();
        current = resolve(current, nextClause, pivot, bfmgr); // Perform resolution step
      }

      // Store the resolved formula in the current node
      ((Mathsat5Proof) node).setFormula(current);
    }
  }

  // Perform resolution between two clauses using a given pivot
  private BooleanFormula resolve(
      BooleanFormula clause1,
      BooleanFormula clause2,
      BooleanFormula pivot,
      BooleanFormulaManager bfmgr) {
    List<BooleanFormula> literals1 = flattenLiterals(clause1, bfmgr);
    List<BooleanFormula> literals2 = flattenLiterals(clause2, bfmgr);

    // Use LinkedHashSet to maintain order and uniqueness
    Set<BooleanFormula> combined = new LinkedHashSet<>();

    // Add literals from first clause, filtering out the pivot/complement
    for (BooleanFormula lit : literals1) {
      if (!lit.equals(pivot) && !isComplement(lit, pivot, bfmgr)) {
        combined.add(lit);
      }
    }

    // Add literals from second clause, filtering out the pivot/complement
    for (BooleanFormula lit : literals2) {
      if (!lit.equals(pivot) && !isComplement(lit, pivot, bfmgr)) {
        combined.add(lit);
      }
    }

    if (combined.isEmpty()) {
      return bfmgr.makeFalse();
    } else if (combined.size() == 1) {
      return combined.iterator().next();
    } else {
      return bfmgr.or(new ArrayList<>(combined));
    }
  }

  // Helper method to flatten an OR-formula into a list of disjunctive literals.
  // Correctly treats AND and other operators as atomic literals for resolution purposes.
  private List<BooleanFormula> flattenLiterals(
      BooleanFormula formula, BooleanFormulaManager bfmgr) {
    List<BooleanFormula> result = new ArrayList<>();

    bfmgr.visit(
        formula,
        new BooleanFormulaVisitor<>() {
          @Override
          public TraversalProcess visitOr(List<BooleanFormula> operands) {
            for (BooleanFormula op : operands) {
              result.addAll(flattenLiterals(op, bfmgr));
            }
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitAnd(List<BooleanFormula> operands) {
            result.add(formula);
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitNot(BooleanFormula operand) {
            result.add(formula);
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitAtom(
              BooleanFormula atom, FunctionDeclaration<BooleanFormula> decl) {
            result.add(formula);
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitXor(BooleanFormula first, BooleanFormula second) {
            result.add(formula);
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitEquivalence(BooleanFormula first, BooleanFormula second) {
            result.add(formula);
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitImplication(BooleanFormula first, BooleanFormula second) {
            result.add(formula);
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitIfThenElse(
              BooleanFormula c, BooleanFormula t, BooleanFormula e) {
            result.add(formula);
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitQuantifier(
              Quantifier q, BooleanFormula qBody, List<Formula> vars, BooleanFormula body) {
            result.add(formula);
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitConstant(boolean value) {
            result.add(formula);
            return TraversalProcess.SKIP;
          }
        });

    return result;
  }

  // Check whether two formulas are logical complements using the FormulaManager
  private boolean isComplement(BooleanFormula a, BooleanFormula b, BooleanFormulaManager bfmgr) {
    return bfmgr.not(a).equals(b) || bfmgr.not(b).equals(a);
  }
}
