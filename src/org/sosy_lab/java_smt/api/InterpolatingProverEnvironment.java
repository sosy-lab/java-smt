// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import java.util.Collection;
import java.util.List;

/**
 * This class provides an interface to an incremental SMT solver with methods for pushing and
 * popping formulas as well as SAT checks. Furthermore, interpolants can be generated for an
 * unsatisfiable list of formulas.
 *
 * @see ProverEnvironment The non-interpolating ProverEnvironment for general notes that also apply
 *     to this interface.
 * @param <T> The type of the objects which can be used to select formulas for interpolant creation.
 */
public interface InterpolatingProverEnvironment<T> extends BasicProverEnvironment<T> {

  /**
   * Get an interpolant for two groups of formulas. This should be called only immediately after an
   * {@link #isUnsat()} call that returned <code>true</code>.
   *
   * <p>There is no direct guarantee that the interpolants returned are part of an inductive
   * sequence', however this seems to work for most solvers as long as the same proof is used, i.e.
   * all interpolants are computed after the same SAT-check. If a solver does not use the same
   * internal proof for several interpolation queries (such as CVC5), then the returned interpolants
   * might not satisfy the sequence-criteria. We suggest the proper method {@link
   * #getSeqInterpolants} for that case.
   *
   * @param formulasOfA A collection of values returned by {@link #push(BooleanFormula)}. All the
   *     corresponding formulas from group A, the remaining formulas form group B.
   * @return An interpolant for A and B
   * @throws SolverException if interpolant cannot be computed, for example because interpolation
   *     procedure is incomplete
   */
  BooleanFormula getInterpolant(Collection<T> formulasOfA)
      throws SolverException, InterruptedException;

  /**
   * This method returns interpolants of an 'inductive sequence'. This property must be supported by
   * the interpolation-strategy of the underlying SMT-solver! Depending on the underlying SMT-solver
   * this method might be faster than N direct calls to getInterpolant().
   *
   * <p>The prover stack should contain the partitioned formulas, but any order is allowed. For an
   * input of N partitions we return N-1 interpolants. Any asserted formula that is on the prover
   * stack and not part of the partitioned list, will be used for background theory and its symbols
   * can appear in any interpolant.
   *
   * @return a 'inductive sequence' of interpolants, such that the implication {@code AND(I_i, P_i)
   *     => I_(i+1)} is satisfied for all i, where P_i is the conjunction of all formulas in
   *     partition i.
   * @throws SolverException if interpolant cannot be computed, for example because interpolation
   *     procedure is incomplete
   */
  default List<BooleanFormula> getSeqInterpolants(List<? extends Collection<T>> partitionedFormulas)
      throws SolverException, InterruptedException {
    // a 'tree' with all subtrees starting at 0 is called a 'sequence'
    return getTreeInterpolants(partitionedFormulas, new int[partitionedFormulas.size()]);
  }

  /**
   * This utility method wraps each formula in a collection and then forwards to {@link
   * #getSeqInterpolants}.
   *
   * @see #getSeqInterpolants
   */
  default List<BooleanFormula> getSeqInterpolants0(List<T> formulas)
      throws SolverException, InterruptedException {
    return getSeqInterpolants(Lists.transform(formulas, ImmutableSet::of));
  }

  /**
   * Compute a sequence of interpolants. The nesting array describes the start of the subtree for
   * tree interpolants. For inductive sequences of interpolants use a nesting array completely
   * filled with 0.
   *
   * <p>Example:
   *
   * <pre>
   * A  D
   * |  |
   * B  E
   * | /
   * C
   * |
   * F  H
   * | /
   * G
   *
   * arrayIndex     = [0,1,2,3,4,5,6,7]  // only for demonstration, not needed
   * partition      = [A,B,D,E,C,F,H,G]  // post-order of tree
   * startOfSubTree = [0,0,2,2,0,0,6,0]  // index of left-most leaf of the current element
   * </pre>
   *
   * <p>The prover stack should contain the partitioned formulas. For an input of N partitions
   * (nodes in the tree) we return N-1 interpolants (one interpolant for/below each node except the
   * root). Any asserted formula that is on the prover stack and not part of the partitioned list,
   * will be used for background theory and its symbols can appear in any interpolant.
   *
   * @param partitionedFormulas of formulas
   * @param startOfSubTree The start of the subtree containing the formula at this index as root.
   * @return Tree interpolants respecting the nesting relation.
   * @throws SolverException if interpolant cannot be computed, for example because interpolation
   *     procedure is incomplete
   */
  List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<T>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException;

  /**
   * This utility method wraps each formula in a collection and then forwards to {@link
   * #getTreeInterpolants}.
   *
   * @see #getTreeInterpolants
   */
  default List<BooleanFormula> getTreeInterpolants0(List<T> formulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    return getTreeInterpolants(Lists.transform(formulas, ImmutableSet::of), startOfSubTree);
  }

  /** Checks for a valid subtree-structure. This code is taken from SMTinterpol. */
  static boolean checkTreeStructure(int numOfPartitions, int[] startOfSubTree) {
    Preconditions.checkArgument(numOfPartitions > 0, "at least one partition should be available.");
    Preconditions.checkArgument(
        numOfPartitions == startOfSubTree.length,
        "partitions and subtree table must have equal length.");
    for (int i = 0; i < numOfPartitions; i++) {
      Preconditions.checkArgument(startOfSubTree[i] >= 0, "tree contains negative node.");
      int j = i;
      while (startOfSubTree[i] < j) {
        j = startOfSubTree[j - 1];
      }
      Preconditions.checkArgument(startOfSubTree[i] == j, "invalid leaf of tree.");
    }
    Preconditions.checkArgument(startOfSubTree[numOfPartitions - 1] == 0, "invalid root of tree.");

    return true;
  }
}
