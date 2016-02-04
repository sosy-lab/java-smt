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

import static org.sosy_lab.solver.z3.Z3NativeApi.ast_vector_get;
import static org.sosy_lab.solver.z3.Z3NativeApi.compute_interpolant;
import static org.sosy_lab.solver.z3.Z3NativeApi.dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_and;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_interpolant;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_params;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_solver;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_assert;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_check;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_get_model;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_get_num_scopes;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_pop;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_push;
import static org.sosy_lab.solver.z3.Z3NativeApi.solver_set_params;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import com.google.common.primitives.Longs;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.z3.Z3NativeApi.PointerToLong;
import org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_LBOOL;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Set;

class Z3InterpolatingProver extends Z3AbstractProver<Long>
    implements InterpolatingProverEnvironment<Long> {

  private final long z3solver;

  private int level = 0;
  private final Deque<Long> assertedFormulas = new ArrayDeque<>();

  Z3InterpolatingProver(Z3FormulaCreator creator, long z3params) {
    super(creator);
    this.z3solver = mk_solver(z3context);
    solver_inc_ref(z3context, z3solver);
    solver_set_params(z3context, z3solver, z3params);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(solver_get_num_scopes(z3context, z3solver) >= 1);
    level--;

    assertedFormulas.removeLast();
    solver_pop(z3context, z3solver, 1);
  }

  @Override
  public Long addConstraint(BooleanFormula f) {
    Preconditions.checkState(!closed);
    trackConstraint(f);
    long e = creator.extractInfo(f);
    inc_ref(z3context, e);
    solver_assert(z3context, z3solver, e);
    assertedFormulas.addLast(e);
    dec_ref(z3context, e);
    return e;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    level++;
    solver_push(z3context, z3solver);
  }

  @Override
  public boolean isUnsat() throws Z3SolverException {
    Preconditions.checkState(!closed);
    int result = solver_check(z3context, z3solver);

    Preconditions.checkState(result != Z3_LBOOL.Z3_L_UNDEF.status);
    return result == Z3_LBOOL.Z3_L_FALSE.status;
  }

  @Override
  @SuppressWarnings({"unchecked", "varargs"})
  public BooleanFormula getInterpolant(final List<Long> formulasOfA) {
    Preconditions.checkState(!closed);

    // calc difference: formulasOfB := assertedFormulas - formulasOfA
    // we have to handle equal formulas on the stack,
    // so we copy the whole stack and remove the formulas of A once.
    final List<Long> formulasOfB = Lists.newLinkedList(assertedFormulas);
    for (long af : formulasOfA) {
      boolean check = formulasOfB.remove(af); // remove only first occurrence
      assert check : "formula from A must be part of all asserted formulas";
    }

    // binary interpolant is a sequence interpolant of only 2 elements
    return Iterables.getOnlyElement(
        getSeqInterpolants(
            ImmutableList.<Set<Long>>of(
                Sets.newHashSet(formulasOfA), Sets.newHashSet(formulasOfB))));
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<Set<Long>> partitionedFormulas) {
    Preconditions.checkState(!closed);
    Preconditions.checkArgument(
        partitionedFormulas.size() >= 2, "at least 2 partitions needed for interpolation");

    // a 'tree' with all subtrees starting at 0 is called a 'sequence'
    return getTreeInterpolants(partitionedFormulas, new int[partitionedFormulas.size()]);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<Set<Long>> partitionedFormulas, int[] startOfSubTree) {
    Preconditions.checkState(!closed);
    final long[] conjunctionFormulas = new long[partitionedFormulas.size()];

    // build conjunction of each partition
    for (int i = 0; i < partitionedFormulas.size(); i++) {
      Preconditions.checkState(!partitionedFormulas.get(i).isEmpty());
      long conjunction = mk_and(z3context, Longs.toArray(partitionedFormulas.get(i)));
      inc_ref(z3context, conjunction);
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
        conjunction = mk_and(z3context, Longs.toArray(children));
      }

      final long interpolationPoint;
      if (i == startOfSubTree.length - 1) {
        // the last node in the tree (=root) does not need the interpolation-point-flag
        interpolationPoint = conjunction;
        Preconditions.checkState(currentSubtree == 0, "subtree of root should start at 0.");
        Preconditions.checkState(stack.isEmpty(), "root should be the last element in the stack.");
      } else {
        interpolationPoint = mk_interpolant(z3context, conjunction);
      }

      inc_ref(z3context, interpolationPoint);
      interpolationFormulas[i] = interpolationPoint;
      stack.addLast(new Z3TreeInterpolant(currentSubtree, interpolationPoint));
      lastSubtree = currentSubtree;
    }

    Preconditions.checkState(
        stack.peekLast().getRootOfTree() == 0, "subtree of root should start at 0.");
    long root = stack.pollLast().getInterpolationPoint();
    Preconditions.checkState(
        stack.isEmpty(), "root should have been the last element in the stack.");

    final PointerToLong model = new PointerToLong();
    final PointerToLong interpolant = new PointerToLong();
    int isSat =
        compute_interpolant(
            z3context,
            root, // last element is end of chain (root of tree)
            mk_params(z3context),
            interpolant,
            model);

    Preconditions.checkState(
        isSat == Z3_LBOOL.Z3_L_FALSE.status,
        "interpolation not possible, because SAT-check returned status '%s'",
        isSat);

    // n partitions -> n-1 interpolants
    // the given tree interpolants are sorted in post-order,
    // so we only need to copy them
    final List<BooleanFormula> result = new ArrayList<>();
    for (int i = 0; i < partitionedFormulas.size() - 1; i++) {
      result.add(creator.encapsulateBoolean(ast_vector_get(z3context, interpolant.value, i)));
    }

    // cleanup
    for (long partition : conjunctionFormulas) {
      dec_ref(z3context, partition);
    }
    for (long partition : interpolationFormulas) {
      dec_ref(z3context, partition);
    }

    return result;
  }

  @Override
  protected long getZ3Model() {
    return solver_get_model(z3context, z3solver);
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);

    while (level > 0) {
      pop();
    }
    assertedFormulas.clear();

    //TODO solver_reset(z3context, z3solver);
    solver_dec_ref(z3context, z3solver);
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
}
