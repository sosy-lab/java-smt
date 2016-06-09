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
package org.sosy_lab.solver.z3;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Sets;
import com.google.common.primitives.Longs;
import com.microsoft.z3.Native;
import com.microsoft.z3.enumerations.Z3_lbool;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

class Z3InterpolatingProver extends Z3AbstractProver<Long>
    implements InterpolatingProverEnvironment<Long> {

  private final long z3solver;

  private int level = 0;
  private final Deque<List<Long>> assertedFormulas = new ArrayDeque<>();

  Z3InterpolatingProver(
      Z3FormulaCreator creator, long z3params, ShutdownNotifier pShutdownNotifier) {
    super(creator, pShutdownNotifier);
    this.z3solver = Native.mkSolver(z3context);
    Native.solverIncRef(z3context, z3solver);
    Native.solverSetParams(z3context, z3solver, z3params);

    // add basic level, needed for addConstraints(f) without previous push()
    assertedFormulas.push(new ArrayList<>());
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(Native.solverGetNumScopes(z3context, z3solver) >= 1);
    Preconditions.checkState(level == assertedFormulas.size() - 1);
    level--;
    assertedFormulas.pop();
    Native.solverPop(z3context, z3solver, 1);
  }

  @Override
  public Long addConstraint(BooleanFormula f) {
    Preconditions.checkState(!closed);
    long e = creator.extractInfo(f);
    Native.incRef(z3context, e);
    Native.solverAssert(z3context, z3solver, e);
    assertedFormulas.peek().add(e);
    Native.decRef(z3context, e);
    return e;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(level == assertedFormulas.size() - 1);
    level++;
    assertedFormulas.push(new ArrayList<>());
    Native.solverPush(z3context, z3solver);
  }

  @Override
  public boolean isUnsat() throws Z3SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    int result = Native.solverCheck(z3context, z3solver);
    shutdownNotifier.shutdownIfNecessary();
    Preconditions.checkState(result != Z3_lbool.Z3_L_UNDEF.toInt());
    return result == Z3_lbool.Z3_L_FALSE.toInt();
  }

  @Override
  @SuppressWarnings({"unchecked", "varargs"})
  public BooleanFormula getInterpolant(final List<Long> formulasOfA) throws InterruptedException {
    Preconditions.checkState(!closed);

    // calc difference: formulasOfB := assertedFormulas - formulasOfA
    // we have to handle equal formulas on the stack,
    // so we copy the whole stack and remove the formulas of A once.
    final List<Long> formulasOfB = new LinkedList<>();
    assertedFormulas.forEach(formulasOfB::addAll);
    for (long af : formulasOfA) {
      boolean check = formulasOfB.remove(af); // remove only first occurrence
      assert check : "formula from A must be part of all asserted formulas";
    }

    // binary interpolant is a sequence interpolant of only 2 elements
    return Iterables.getOnlyElement(
        getSeqInterpolants(
            ImmutableList.of(Sets.newHashSet(formulasOfA), Sets.newHashSet(formulasOfB))));
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<Set<Long>> partitionedFormulas)
      throws InterruptedException {
    Preconditions.checkState(!closed);
    Preconditions.checkArgument(
        partitionedFormulas.size() >= 2, "at least 2 partitions needed for interpolation");

    // a 'tree' with all subtrees starting at 0 is called a 'sequence'
    return getTreeInterpolants(partitionedFormulas, new int[partitionedFormulas.size()]);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<Set<Long>> partitionedFormulas, int[] startOfSubTree) throws InterruptedException {
    Preconditions.checkState(!closed);
    final long[] conjunctionFormulas = new long[partitionedFormulas.size()];

    // build conjunction of each partition
    for (int i = 0; i < partitionedFormulas.size(); i++) {
      long conjunction =
          Native.mkAnd(
              z3context,
              partitionedFormulas.get(i).size(),
              Longs.toArray(partitionedFormulas.get(i)));
      Native.incRef(z3context, conjunction);
      conjunctionFormulas[i] = conjunction;
    }

    // build tree of interpolation-points
    final long[] interpolationFormulas = new long[partitionedFormulas.size()];
    final Deque<Z3TreeInterpolant> stack = new ArrayDeque<>();

    int lastSubtree = -1; // subtree starts with 0. With -1<0 we start a new subtree.
    for (int i = 0; i < startOfSubTree.length; i++) {
      final int currentSubtree = startOfSubTree[i];
      final long conjunction;
      if (currentSubtree > lastSubtree) {
        // start of a new subtree -> first element has no children
        conjunction = conjunctionFormulas[i];

      } else { // if (currentSubtree <= lastSubtree) {
        // merge-point in tree, several children at a node -> pop from stack and conjunct
        final List<Long> children = new ArrayList<>();
        while (!stack.isEmpty() && currentSubtree <= stack.peekLast().getRootOfTree()) {
          // adding at front is important for tree-structure!
          children.add(0, stack.pollLast().getInterpolationPoint());
        }
        children.add(conjunctionFormulas[i]); // add the node itself
        conjunction = Native.mkAnd(z3context, 2, Longs.toArray(children));
      }

      final long interpolationPoint;
      if (i == startOfSubTree.length - 1) {
        // the last node in the tree (=root) does not need the interpolation-point-flag
        interpolationPoint = conjunction;
        Preconditions.checkState(currentSubtree == 0, "subtree of root should start at 0.");
        Preconditions.checkState(stack.isEmpty(), "root should be the last element in the stack.");
      } else {
        interpolationPoint = Native.mkInterpolant(z3context, conjunction);
      }

      Native.incRef(z3context, interpolationPoint);
      interpolationFormulas[i] = interpolationPoint;
      stack.addLast(new Z3TreeInterpolant(currentSubtree, interpolationPoint));
      lastSubtree = currentSubtree;
    }

    Preconditions.checkState(
        stack.peekLast().getRootOfTree() == 0, "subtree of root should start at 0.");
    long root = stack.pollLast().getInterpolationPoint();
    Preconditions.checkState(
        stack.isEmpty(), "root should have been the last element in the stack.");

    final long proof = Native.solverGetProof(z3context, z3solver);
    Native.incRef(z3context, proof);

    long interpolationResult =
        Native.getInterpolant(
            z3context,
            proof, //refutation of premises := proof
            root, // last element is end of chain (root of tree), pattern := interpolation tree
            Native.mkParams(z3context));

    shutdownNotifier.shutdownIfNecessary();

    // n partitions -> n-1 interpolants
    // the given tree interpolants are sorted in post-order,
    // so we only need to copy them
    final List<BooleanFormula> result = new ArrayList<>();
    for (int i = 0; i < partitionedFormulas.size() - 1; i++) {
      result.add(
          creator.encapsulateBoolean(Native.astVectorGet(z3context, interpolationResult, i)));
    }

    // cleanup
    Native.decRef(z3context, proof);
    for (long partition : conjunctionFormulas) {
      Native.decRef(z3context, partition);
    }
    for (long partition : interpolationFormulas) {
      Native.decRef(z3context, partition);
    }

    return result;
  }

  @Override
  protected long getZ3Model() {
    return Native.solverGetModel(z3context, z3solver);
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);

    while (level > 0) {
      pop();
    }

    Preconditions.checkState(assertedFormulas.size() == 1);
    assertedFormulas.clear();

    //TODO solver_reset(z3context, z3solver);
    Native.solverDecRef(z3context, z3solver);
    closed = true;
  }

  private static class Z3TreeInterpolant {
    private final int rootOfSubTree;
    private final long interpolationPoint;

    private Z3TreeInterpolant(int pRootOfSubtree, long pInterpolationPoint) {
      rootOfSubTree = pRootOfSubtree;
      interpolationPoint = pInterpolationPoint;
    }

    private int getRootOfTree() {
      return rootOfSubTree;
    }

    private long getInterpolationPoint() {
      return interpolationPoint;
    }
  }

  @Override
  public String toString() {
    Preconditions.checkState(!closed);
    return Native.solverToString(z3context, z3solver);
  }
}
