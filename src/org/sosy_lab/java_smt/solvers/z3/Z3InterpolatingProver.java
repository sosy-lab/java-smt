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
package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Sets;
import com.google.common.primitives.Longs;
import com.microsoft.z3.Native;
import com.microsoft.z3.Z3Exception;

import org.sosy_lab.common.io.MoreFiles;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

import java.io.IOException;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;

import javax.annotation.Nullable;

class Z3InterpolatingProver extends Z3SolverBasedProver<Long>
    implements InterpolatingProverEnvironment<Long> {

  private final LogManager logger;

  private final @Nullable PathCounterTemplate dumpFailedInterpolationQueries;
  private final Deque<List<Long>> assertedFormulas = new ArrayDeque<>();

  Z3InterpolatingProver(
      Z3FormulaCreator creator,
      long z3params,
      LogManager pLogger,
      @Nullable PathCounterTemplate pDumpFailedInterpolationQueries) {
    super(creator, z3params);
    logger = pLogger;
    dumpFailedInterpolationQueries = pDumpFailedInterpolationQueries;

    // add basic level, needed for addConstraints(f) without previous push()
    assertedFormulas.push(new ArrayList<>());
  }

  @Override
  public void pop() {
    Preconditions.checkState(getLevel() == assertedFormulas.size() - 1);
    super.pop();
    assertedFormulas.pop();
  }

  @Override
  public Long addConstraint(BooleanFormula f) {
    long e = super.addConstraint0(f);
    assertedFormulas.peek().add(e);
    return e;
  }

  @Override
  public void push() {
    Preconditions.checkState(getLevel() == assertedFormulas.size() - 1);
    super.push();
    assertedFormulas.push(new ArrayList<>());
  }

  @Override
  @SuppressWarnings({"unchecked", "varargs"})
  public BooleanFormula getInterpolant(final List<Long> formulasOfA)
      throws InterruptedException, SolverException {
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
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    Preconditions.checkArgument(
        partitionedFormulas.size() >= 2, "at least 2 partitions needed for interpolation");

    // a 'tree' with all subtrees starting at 0 is called a 'sequence'
    return getTreeInterpolants(partitionedFormulas, new int[partitionedFormulas.size()]);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<Set<Long>> partitionedFormulas, int[] startOfSubTree)
      throws InterruptedException, SolverException {
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
        while (!stack.isEmpty() && currentSubtree <= stack.peek().getRootOfTree()) {
          // adding at front is important for tree-structure!
          children.add(0, stack.pop().getInterpolationPoint());
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
        stack.isEmpty(), "root should have been the last element in the stack.");

    final long proof = Native.solverGetProof(z3context, z3solver);
    Native.incRef(z3context, proof);

    long interpolationResult;
    try {
      interpolationResult =
          Native.getInterpolant(
              z3context,
              proof, //refutation of premises := proof
              root, // last element is end of chain (root of tree), pattern := interpolation tree
              Native.mkParams(z3context));
    } catch (Z3Exception e) {
      if (dumpFailedInterpolationQueries != null && !creator.shutdownNotifier.shouldShutdown()) {
        try (Writer dumpFile =
            MoreFiles.openOutputFile(
                dumpFailedInterpolationQueries.getFreshPath(), StandardCharsets.UTF_8)) {
          dumpFile.write(Native.solverToString(z3context, z3solver));
          dumpFile.write("\n(compute-interpolant ");
          dumpFile.write(Native.astToString(z3context, root));
          dumpFile.write(")\n");
        } catch (IOException e2) {
          logger.logUserException(
              Level.WARNING, e2, "Could not dump failed interpolation query to file");
        }
      }
      if ("theory not supported by interpolation or bad proof".equals(e.getMessage())) {
        throw new SolverException(e.getMessage(), e);
      }
      throw creator.handleZ3Exception(e);
    }

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

    checkInterpolantsForUnboundVariables(result); // Do this last after cleanup.

    return result;
  }

  /**
   * Check whether any formula in a given list contains unbound variables.
   * Z3 has the problem that it sometimes returns such invalid formulas as interpolants
   * (https://github.com/Z3Prover/z3/issues/665).
   */
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

  @Override
  public void close() {
    super.close();
    Preconditions.checkState(assertedFormulas.size() == 1);
    assertedFormulas.clear();
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
