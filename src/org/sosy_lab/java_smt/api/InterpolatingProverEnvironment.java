/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.api;

import com.google.common.base.Preconditions;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.List;
import java.util.Set;

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
   * Add a formula to the environment stack, asserting it. The returned value can be used when
   * selecting the formulas for interpolant generation.
   */
  @Override
  @CanIgnoreReturnValue
  default T push(BooleanFormula f) throws InterruptedException {
    // Java8 does not support overriding of default-interface-methods,
    // thus we forward to the super-interface here.
    return BasicProverEnvironment.super.push(f);
  }

  /**
   * Get an interpolant for two groups of formulas. This should be called only immediately after an
   * {@link #isUnsat()} call that returned <code>true</code>.
   *
   * <p>There is no direct guarantee that the interpolants returned are part of an inductive
   * sequence', however this seems to work for most (all?) solvers as long as the same proof is
   * used, i.e. all interpolants are computed after the same SAT-check.
   *
   * @param formulasOfA A list of values returned by {@link #push(BooleanFormula)}. All the
   *     corresponding formulas from group A, the remaining formulas form group B.
   * @return An interpolant for A and B
   * @throws SolverException if interpolant cannot be computed, for example because interpolation
   *     procedure is incomplete
   */
  BooleanFormula getInterpolant(List<T> formulasOfA) throws SolverException, InterruptedException;

  /**
   * This method returns interpolants of an 'inductive sequence'. This property must be supported by
   * the interpolation-strategy of the underlying SMT-solver! Depending on the underlying SMT-solver
   * this method might be faster than N direct calls to getInterpolant().
   *
   * <p>The stack must contain exactly the partitioned formulas, but any order is allowed. For an
   * input of N partitions we return N-1 interpolants.
   *
   * @return a 'inductive sequence' of interpolants, such that the implication {@code AND(I_i, P_i)
   *     => I_(i+1)} is satisfied for all i, where P_i is the conjunction of all formulas in
   *     partition i.
   * @throws SolverException if interpolant cannot be computed, for example because interpolation
   *     procedure is incomplete
   */
  List<BooleanFormula> getSeqInterpolants(List<Set<T>> partitionedFormulas)
      throws SolverException, InterruptedException;

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
   * @param partitionedFormulas of formulas
   * @param startOfSubTree The start of the subtree containing the formula at this index as root.
   * @return Tree interpolants respecting the nesting relation.
   * @throws SolverException if interpolant cannot be computed, for example because interpolation
   *     procedure is incomplete
   */
  List<BooleanFormula> getTreeInterpolants(List<Set<T>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException;

  /** Checks for a valid subtree-structure. This code is taken from SMTinterpol. */
  static boolean checkTreeStructure(int numOfPartitions, int[] startOfSubTree) {
    Preconditions.checkArgument(
        numOfPartitions == startOfSubTree.length,
        "partitions and subtree table mus have equal length.");
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
