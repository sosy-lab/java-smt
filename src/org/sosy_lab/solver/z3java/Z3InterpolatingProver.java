/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.solver.z3java;

import static org.sosy_lab.solver.z3java.Z3BooleanFormulaManager.toBool;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.InterpolationContext;
import com.microsoft.z3.InterpolationContext.ComputeInterpolantResult;
import com.microsoft.z3.Model;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_lbool;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Set;

class Z3InterpolatingProver extends Z3AbstractProver<Expr>
    implements InterpolatingProverEnvironment<Expr> {

  private final Solver z3solver;

  private int level = 0;
  private final Deque<BoolExpr> assertedFormulas = new ArrayDeque<>();

  Z3InterpolatingProver(
      Z3FormulaCreator creator, Params z3params, ShutdownNotifier pShutdownNotifier) {
    super(creator, pShutdownNotifier);
    this.z3solver = z3context.mkSolver();
    z3solver.setParameters(z3params);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(z3solver.getNumScopes() >= 1);
    level--;

    assertedFormulas.removeLast();
    z3solver.pop();
  }

  @Override
  public Expr addConstraint(BooleanFormula f) {
    Preconditions.checkState(!closed);
    trackConstraint(f);
    BoolExpr e = (BoolExpr) creator.extractInfo(f);
    z3solver.add(e);
    assertedFormulas.addLast(e);
    return e;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    level++;
    z3solver.push();
  }

  @Override
  public boolean isUnsat() throws InterruptedException {
    Preconditions.checkState(!closed);
    Status result = z3solver.check();
    shutdownNotifier.shutdownIfNecessary();
    Preconditions.checkArgument(result != Status.UNKNOWN);
    return result == Status.UNSATISFIABLE;
  }

  @Override
  @SuppressWarnings({"unchecked", "varargs"})
  public BooleanFormula getInterpolant(final List<Expr> formulasOfA)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);

    // calc difference: formulasOfB := assertedFormulas - formulasOfA
    // we have to handle equal formulas on the stack,
    // so we copy the whole stack and remove the formulas of A once.
    final List<Expr> formulasOfB = Lists.<Expr>newLinkedList(assertedFormulas);
    for (Expr af : formulasOfA) {
      boolean check = formulasOfB.remove(af); // remove only first occurrence
      assert check : "formula from A must be part of all asserted formulas";
    }

    // binary interpolant is a sequence interpolant of only 2 elements
    return Iterables.getOnlyElement(
        getSeqInterpolants(
            ImmutableList.<Set<Expr>>of(
                Sets.newHashSet(formulasOfA), Sets.newHashSet(formulasOfB))));
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<Set<Expr>> partitionedFormulas)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    Preconditions.checkArgument(
        partitionedFormulas.size() >= 2, "at least 2 partitions needed for interpolation");

    // a 'tree' with all subtrees starting at 0 is called a 'sequence'
    return getTreeInterpolants(partitionedFormulas, new int[partitionedFormulas.size()]);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<Set<Expr>> partitionedFormulas, int[] startOfSubTree)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);

    try {
      final BoolExpr[] conjunctionFormulas = new BoolExpr[partitionedFormulas.size()];

      // build conjunction of each partition
      for (int i = 0; i < partitionedFormulas.size(); i++) {
        Preconditions.checkState(!partitionedFormulas.get(i).isEmpty());
        BoolExpr conjunction = z3context.mkAnd(toBool(partitionedFormulas.get(i)));
        conjunctionFormulas[i] = conjunction;
      }

      // build tree of interpolation-points
      final Deque<Z3TreeInterpolant> stack = new ArrayDeque<>();

      int lastSubtree = -1; // subtree starts with 0. With -1<0 we start a new subtree.
      for (int i = 0; i < startOfSubTree.length; i++) {
        final int currentSubtree = startOfSubTree[i];
        final BoolExpr conjunction;
        if (currentSubtree > lastSubtree) {
          // start of a new subtree -> first element has no children
          conjunction = conjunctionFormulas[i];

        } else { // if (currentSubtree <= lastSubtree) {
          // merge-point in tree, several children at a node -> pop from stack and conjunct
          final List<BoolExpr> children = new ArrayList<>();
          while (!stack.isEmpty() && currentSubtree <= stack.peekLast().getRootOfTree()) {
            // adding at front is important for tree-structure!
            children.add(0, stack.pollLast().getInterpolationPoint());
          }
          children.add(conjunctionFormulas[i]); // add the node itself
          conjunction = z3context.mkAnd(toBool(children));
        }

        final BoolExpr interpolationPoint;
        if (i == startOfSubTree.length - 1) {
          // the last node in the tree (=root) does not need the interpolation-point-flag
          interpolationPoint = conjunction;
          Preconditions.checkState(currentSubtree == 0, "subtree of root should start at 0.");
          Preconditions.checkState(
              stack.isEmpty(), "root should be the last element in the stack.");
        } else {
          interpolationPoint = ((InterpolationContext) z3context).MkInterpolant(conjunction);
        }

        stack.addLast(new Z3TreeInterpolant(currentSubtree, interpolationPoint));
        lastSubtree = currentSubtree;
      }

      Preconditions.checkState(
          stack.peekLast().getRootOfTree() == 0, "subtree of root should start at 0.");
      BoolExpr root = stack.pollLast().getInterpolationPoint();
      Preconditions.checkState(
          stack.isEmpty(), "root should have been the last element in the stack.");

      ComputeInterpolantResult interpolationResult =
          ((InterpolationContext) z3context).ComputeInterpolant(root, z3context.mkParams());

      shutdownNotifier.shutdownIfNecessary();

      Preconditions.checkState(
          interpolationResult.status == Z3_lbool.Z3_L_FALSE,
          "interpolation not possible, because SAT-check returned status '%s'",
          interpolationResult);

      // n partitions -> n-1 interpolants
      // the given tree interpolants are sorted in post-order,
      // so we only need to copy them
      final List<BooleanFormula> result = new ArrayList<>();
      for (int i = 0; i < partitionedFormulas.size() - 1; i++) {
        result.add(creator.encapsulateBoolean(interpolationResult.interp[i]));
      }

      return result;
    } catch (Z3Exception e) {
      shutdownNotifier.shutdownIfNecessary();
      throw new SolverException("Z3 had a problem during interpolation computation", e);
    }
  }

  @Override
  protected Model getZ3Model() {
    return z3solver.getModel();
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);

    while (level > 0) {
      pop();
    }
    assertedFormulas.clear();

    closed = true;
  }

  private static class Z3TreeInterpolant {
    private final int rootOfSubTree;
    private final BoolExpr interpolationPoint;

    private Z3TreeInterpolant(int pRootOfSubtree, BoolExpr pInterpolationPoint) {
      rootOfSubTree = pRootOfSubtree;
      interpolationPoint = pInterpolationPoint;
    }

    private int getRootOfTree() {
      return rootOfSubTree;
    }

    private BoolExpr getInterpolationPoint() {
      return interpolationPoint;
    }
  }
}
