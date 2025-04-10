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

import com.google.common.base.Preconditions;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
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
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.basicimpl.ProofFactory;
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
  public ProofNode getProof() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(this.isUnsat());

    ProofNode pn;
    long pm = msat_get_proof_manager(curEnv);
    long proof = msat_get_proof(pm);
    pn = Mathsat5ProofNode.fromMsatProof(this, proof);
    context.getFormulaManager().getBooleanFormulaManager();
    clausifyResChain(pn, context.getFormulaManager().getBooleanFormulaManager());
    msat_destroy_proof_manager(pm);

    return pn;

    // return getProof0();
  }

  // update all RES_CHAIN nodes in the proof DAG by computing resolution
  // formulas and return the updated root node with formulas attached.
  private void clausifyResChain(ProofNode root, BooleanFormulaManager bfmgr) {
    Map<ProofNode, Boolean> visited = new HashMap<>(); // Track visited nodes
    Stack<ProofNode> stack = new Stack<>();
    Stack<ProofNode> processStack =
        new Stack<>(); // Stack to hold nodes for post-processing after children

    stack.push(root); // Start with the root node
    visited.put(root, Boolean.FALSE); // Mark root as unvisited

    while (!stack.isEmpty()) {
      ProofNode node = stack.peek(); // Look at the top node, but don't pop yet

      if (visited.get(node) == Boolean.FALSE) {
        // First time visiting this node
        visited.put(node, Boolean.TRUE); // Mark node as visited

        // Push all children onto stack
        List<ProofNode> children = node.getChildren();
        for (int i = children.size() - 1; i >= 0; i--) {
          ProofNode child = children.get(i);
          if (!visited.containsKey(child)) {
            stack.push(child); // Only push unvisited children
            visited.put(child, Boolean.FALSE); // Mark child as unvisited
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
  private void processResChain(ProofNode node, BooleanFormulaManager bfmgr) {
    List<ProofNode> children = node.getChildren();

    // If the current node is a RES_CHAIN, compute the resolved formula
    if (node.getRule().equals(Rule.RES_CHAIN)) {
      // Sanity check: res-chain nodes must have an odd number of children (clause, pivot, clause,
      // ..., clause)
      if (children.size() < 3 || children.size() % 2 == 0) {
        throw new IllegalArgumentException("Invalid res-chain structure: must be odd and >= 3");
      }

      // Begin resolution chain: start with the first clause
      BooleanFormula current = (BooleanFormula) children.get(0).getFormula();

      // Apply resolution iteratively using pivot, clause pairs
      for (int i = 1; i < children.size() - 1; i += 2) {
        BooleanFormula pivot = (BooleanFormula) children.get(i).getFormula();
        BooleanFormula nextClause = (BooleanFormula) children.get(i + 1).getFormula();
        current = resolve(current, nextClause, pivot, bfmgr); // Perform resolution step
      }

      // Store the resolved formula in the current node
      ((Mathsat5ProofNode) node).setFormula(current);
    }
  }

  // Perform resolution between two  clauses using a given pivot
  private BooleanFormula resolve(
      BooleanFormula clause1,
      BooleanFormula clause2,
      BooleanFormula pivot,
      BooleanFormulaManager bfmgr) {
    List<BooleanFormula> literals1 = flattenLiterals(clause1, bfmgr);
    List<BooleanFormula> literals2 = flattenLiterals(clause2, bfmgr);
    List<BooleanFormula> combined = new ArrayList<>();

    boolean removed = false;

    for (BooleanFormula lit : literals1) {
      if (!isComplement(lit, pivot, bfmgr)) {
        combined.add(lit);
      }
    }

    List<BooleanFormula> temp = new ArrayList<>();
    boolean removed2 = false;
    for (BooleanFormula lit : literals2) {
      if (!isComplement(lit, pivot, bfmgr)) {
        temp.add(lit);
      }
    }

    combined.addAll(temp);

    if (combined.isEmpty()) {
      return bfmgr.makeFalse();
    } else if (combined.size() == 1) {
      return combined.get(0);
    } else {
      return bfmgr.or(combined);
    }
  }

  // Helper method to flatten an OR/AND-formula into a list of disjunctive literals
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
            for (BooleanFormula op : operands) {
              result.addAll(flattenLiterals(op, bfmgr));
            }
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitNot(BooleanFormula operand) {
            result.add(formula); // add original NOT node
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitAtom(
              BooleanFormula atom, FunctionDeclaration<BooleanFormula> decl) {
            result.add(formula); // add original atom
            return TraversalProcess.SKIP;
          }

          // others unchanged...
          @Override
          public TraversalProcess visitXor(BooleanFormula a, BooleanFormula b) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitEquivalence(BooleanFormula a, BooleanFormula b) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitImplication(BooleanFormula a, BooleanFormula b) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitIfThenElse(
              BooleanFormula c, BooleanFormula t, BooleanFormula e) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitQuantifier(
              Quantifier q, BooleanFormula qBody, List<Formula> vars, BooleanFormula body) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitConstant(boolean value) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitBoundVar(BooleanFormula var, int index) {
            return TraversalProcess.SKIP;
          }
        });

    return result;
  }

  // Check whether two formulas are logical complements
  private boolean isComplement(BooleanFormula a, BooleanFormula b, BooleanFormulaManager bfmgr) {
    // Define the visitor to check for complement relation
    final boolean[] isComplement = {false};

    bfmgr.visitRecursively(
        a,
        new BooleanFormulaVisitor<>() {
          @Override
          public TraversalProcess visitNot(BooleanFormula operand) {
            // Check if the negation of 'operand' equals 'b'
            if (operand.equals(b)) {
              isComplement[0] = true;
            }
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitAtom(
              BooleanFormula atom, FunctionDeclaration<BooleanFormula> decl) {
            if (atom.equals(b)) {
              isComplement[0] = true;
            }
            return TraversalProcess.SKIP;
          }

          // Default implementation for other nodes, such as OR, AND, etc.
          @Override
          public TraversalProcess visitOr(List<BooleanFormula> operands) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitAnd(List<BooleanFormula> operands) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitXor(BooleanFormula a, BooleanFormula b) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitEquivalence(BooleanFormula a, BooleanFormula b) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitImplication(BooleanFormula a, BooleanFormula b) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitIfThenElse(
              BooleanFormula c, BooleanFormula t, BooleanFormula e) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitQuantifier(
              Quantifier q, BooleanFormula qBody, List<Formula> vars, BooleanFormula body) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitConstant(boolean value) {
            return TraversalProcess.SKIP;
          }

          @Override
          public TraversalProcess visitBoundVar(BooleanFormula var, int index) {
            return TraversalProcess.SKIP;
          }
        });

    return isComplement[0];
  }

  protected ProofNode getProof0() {
    var proofFactory =
        new ProofFactory<Long>(this, "MATHSAT5") {
          public ProofNode createProofWrapper(long pProof) {
            return this.createProofNode(pProof);
          }
        };
    long pm = msat_get_proof_manager(curEnv);
    long proof = msat_get_proof(pm);
    ProofNode pn = proofFactory.createProofWrapper(proof);
    msat_destroy_proof_manager(pm);
    return pn;
  }
}
