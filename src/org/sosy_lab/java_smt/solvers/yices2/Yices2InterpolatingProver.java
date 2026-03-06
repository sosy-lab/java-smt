/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.yices2;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_assert_formulas;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_context;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_interpolate;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_true;

import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import com.google.common.primitives.Ints;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class Yices2InterpolatingProver extends Yices2AbstractProver<Integer>
    implements InterpolatingProverEnvironment<Integer> {
  protected Yices2InterpolatingProver(
      Yices2FormulaCreator creator,
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier) {
    super(creator, pOptions, pBmgr, pShutdownNotifier);
  }

  @Override
  protected @Nullable Integer addConstraintImpl(BooleanFormula constraint)
      throws InterruptedException {
    return addConstraint0(constraint);
  }

  @Override
  public BooleanFormula getInterpolant(Collection<Integer> formulasOfA)
      throws SolverException, InterruptedException {
    checkGenerateInterpolants();
    checkArgument(
        getAssertedConstraintIds().containsAll(formulasOfA),
        "Interpolation can only be done over previously asserted formulas.");

    var setA = ImmutableSet.copyOf(formulasOfA);
    var setB = Sets.difference(getAssertedConstraintIds(), setA);

    return creator.encapsulateBoolean(
        interpolate(
            FluentIterable.from(setA).transform(stack.peekLast()::get).toSet(),
            FluentIterable.from(setB).transform(stack.peekLast()::get).toSet()));
  }

  private int interpolate(Collection<Integer> setA, Collection<Integer> setB) {
    var ctxA = newContext(true);
    var ctxB = newContext(true);

    yices_assert_formulas(ctxA, setA.size(), Ints.toArray(setA));
    yices_assert_formulas(ctxB, setB.size(), Ints.toArray(setB));

    try {
      return yices_interpolate(ctxA, ctxB);
    } finally {
      yices_free_context(ctxB);
      yices_free_context(ctxA);
    }
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<Integer>> partitions)
      throws SolverException, InterruptedException {
    checkGenerateInterpolants();
    checkArgument(!partitions.isEmpty(), "at least one partition should be available.");
    final Set<Integer> assertedConstraintIds = getAssertedConstraintIds();
    checkArgument(
        partitions.stream().allMatch(assertedConstraintIds::containsAll),
        "interpolation can only be done over previously asserted formulas.");

    final int n = partitions.size();
    final List<BooleanFormula> itps = new ArrayList<>();
    var previousItp = yices_true();
    for (int i = 1; i < n; i++) {
      Collection<Integer> formulasA =
          FluentIterable.from(partitions.get(i - 1))
              .transform(stack.peekLast()::get)
              .append(new Integer[] {previousItp})
              .toSet();
      Collection<Integer> formulasB =
          FluentIterable.concat(partitions.subList(i, n)).transform(stack.peekLast()::get).toSet();
      var itp = interpolate(formulasA, formulasB);
      itps.add(creator.encapsulateBoolean(itp));
      previousItp = itp;
    }
    return itps;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }
}
