/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3legacy;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.primitives.Longs;
import com.microsoft.z3legacy.Native;
import com.microsoft.z3legacy.Z3Exception;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

class Z3LegacyInterpolatingProver extends Z3LegacyAbstractProver<Long>
    implements InterpolatingProverEnvironment<Long> {

  Z3LegacyInterpolatingProver(
      Z3LegacyFormulaCreator pCreator,
      Z3LegacyFormulaManager pMgr,
      Set<ProverOptions> pOptions,
      @Nullable PathCounterTemplate pLogfile,
      ShutdownNotifier pShutdownNotifier) {
    super(pCreator, pMgr, pOptions, pLogfile, pShutdownNotifier);
  }

  @Override
  @SuppressWarnings({"unchecked", "varargs"})
  public BooleanFormula getInterpolant(final Collection<Long> pFormulasOfA)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    checkArgument(
        getAssertedConstraintIds().containsAll(pFormulasOfA),
        "interpolation can only be done over previously asserted formulas.");

    Set<Long> formulasOfA = ImmutableSet.copyOf(pFormulasOfA);

    // calc difference: formulasOfB := assertedFormulas - formulasOfA
    Set<Long> formulasOfB =
        getAssertedConstraintIds().stream()
            .filter(f -> !formulasOfA.contains(f))
            .collect(ImmutableSet.toImmutableSet());

    // binary interpolant is a sequence interpolant of only 2 elements
    return Iterables.getOnlyElement(getSeqInterpolants(ImmutableList.of(formulasOfA, formulasOfB)));
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<Long>> partitionedFormulas, int[] startOfSubTree)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    assert InterpolatingProverEnvironment.checkTreeStructure(
        partitionedFormulas.size(), startOfSubTree);

    final long[] conjunctionFormulas = buildConjunctions(partitionedFormulas);
    final long[] interpolationFormulas =
        buildFormulaTree(partitionedFormulas, startOfSubTree, conjunctionFormulas);
    final long root = interpolationFormulas[interpolationFormulas.length - 1];

    final long proof = Native.solverGetProof(z3context, z3solver);
    Native.incRef(z3context, proof);

    final long interpolationResult = computeInterpolants(root, proof);

    // n partitions -> n-1 interpolants
    // the given tree interpolants are sorted in post-order,
    // so we only need to copy them
    final List<BooleanFormula> result = new ArrayList<>();
    for (int i = 0; i < partitionedFormulas.size() - 1; i++) {
      result.add(
          creator.encapsulateBoolean(Native.astVectorGet(z3context, interpolationResult, i)));
    }
    assert result.size() == startOfSubTree.length - 1;

    // cleanup
    Native.decRef(z3context, proof);
    for (long partition : conjunctionFormulas) {
      Native.decRef(z3context, partition);
    }
    for (long partition : interpolationFormulas) {
      Native.decRef(z3context, partition);
    }

    checkInterpolantsForUnboundVariables(result); // Do this last after cleanup.

    return result;
  }

  /** build a conjunction of each partition. */
  private long[] buildConjunctions(List<? extends Collection<Long>> partitionedFormulas) {
    final long[] conjunctionFormulas = new long[partitionedFormulas.size()];
    for (int i = 0; i < partitionedFormulas.size(); i++) {
      long conjunction =
          Native.mkAnd(
              z3context,
              partitionedFormulas.get(i).size(),
              Longs.toArray(partitionedFormulas.get(i)));
      Native.incRef(z3context, conjunction);
      conjunctionFormulas[i] = conjunction;
    }
    return conjunctionFormulas;
  }

  /** build tree of interpolation-points. */
  private long[] buildFormulaTree(
      List<? extends Collection<Long>> partitionedFormulas,
      int[] startOfSubTree,
      final long[] conjunctionFormulas) {
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
        final Deque<Long> children = new ArrayDeque<>();
        while (!stack.isEmpty() && currentSubtree <= stack.peek().getRootOfTree()) {
          // adding at front is important for tree-structure!
          children.addFirst(stack.pop().getInterpolationPoint());
        }
        children.add(conjunctionFormulas[i]); // add the node itself
        conjunction = Native.mkAnd(z3context, children.size(), Longs.toArray(children));
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
      stack.push(new Z3TreeInterpolant(currentSubtree, interpolationPoint));
      lastSubtree = currentSubtree;
    }

    Preconditions.checkState(
        stack.peek().getRootOfTree() == 0, "subtree of root should start at 0.");
    long root = stack.pop().getInterpolationPoint();
    Preconditions.checkState(
        root == interpolationFormulas[interpolationFormulas.length - 1],
        "subtree of root should start at 0.");
    Preconditions.checkState(
        stack.isEmpty(), "root should have been the last element in the stack.");

    return interpolationFormulas;
  }

  /** compute interpolants for the given tree of formulas and dump the interpolation problem. */
  private long computeInterpolants(final long root, final long proof)
      throws SolverException, InterruptedException {
    long interpolationResult;
    try {
      interpolationResult =
          Native.getInterpolant(
              z3context,
              proof, // refutation of premises := proof
              root, // last element is end of chain (root of tree), pattern := interpolation tree
              Native.mkParams(z3context));
    } catch (Z3Exception e) {
      if ("theory not supported by interpolation or bad proof".equals(e.getMessage())) {
        throw new SolverException(e.getMessage(), e);
      }
      throw creator.handleZ3Exception(e);
    }
    return interpolationResult;
  }

  /**
   * Check whether any formula in a given list contains unbound variables. Z3 has the problem that
   * it sometimes returns such invalid formulas as interpolants
   * (https://github.com/Z3Prover/z3/issues/665).
   */
  @SuppressWarnings("deprecation")
  private void checkInterpolantsForUnboundVariables(List<BooleanFormula> itps)
      throws SolverException {
    List<Formula> unboundVariables = new ArrayList<>(1);
    final DefaultFormulaVisitor<TraversalProcess> unboundVariablesCollector =
        new DefaultFormulaVisitor<TraversalProcess>() {
          @Override
          public TraversalProcess visitBoundVariable(Formula f, int deBruijnIdx) {
            unboundVariables.add(f);
            return TraversalProcess.ABORT;
          }

          @Override
          public TraversalProcess visitQuantifier(
              BooleanFormula pF,
              Quantifier pQ,
              List<Formula> pBoundVariables,
              BooleanFormula pBody) {
            return TraversalProcess.SKIP; // bound variables in quantifiers are probably ok
          }

          @Override
          protected TraversalProcess visitDefault(org.sosy_lab.java_smt.api.Formula pF) {
            return TraversalProcess.CONTINUE;
          }
        };

    for (BooleanFormula itp : itps) {
      creator.visitRecursively(unboundVariablesCollector, itp);
      if (!unboundVariables.isEmpty()) {
        throw new SolverException(
            "Unbound variable " + unboundVariables.get(0) + " in interpolant " + itp);
      }
    }
  }

  private static final class Z3TreeInterpolant {
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
