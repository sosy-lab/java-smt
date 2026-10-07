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

import static org.sosy_lab.common.collect.Collections3.transformedImmutableSetCopy;

import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import com.google.common.primitives.Ints;
import com.sri.yices.InterpolationContext;
import com.sri.yices.Status;
import com.sri.yices.Terms;
import com.sri.yices.YicesException;
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

class Yices2InterpolatingProver extends Yices2AbstractProver<Integer>
    implements InterpolatingProverEnvironment<Integer> {

  private static final ImmutableSet<String> ACCEPTED_INTERPOLATION_ERROR_MESSAGES =
      ImmutableSet.of(
          "mcsat: unsupported theory\n",
          "mcsat: assumption variable has a type that mcsat cannot decide on\n");

  Yices2InterpolatingProver(
      Yices2FormulaCreator creator,
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier,
      String pSolverType) {
    super(creator, pOptions, pBmgr, pShutdownNotifier, pSolverType);
  }

  @Override
  protected @Nullable Integer addConstraintImpl(BooleanFormula constraint)
      throws InterruptedException {
    return addConstraint0(constraint);
  }

  @Override
  public BooleanFormula getInterpolant(Collection<Integer> formulasOfA)
      throws SolverException, InterruptedException {
    var setA = ImmutableSet.copyOf(formulasOfA);
    var setB = Sets.difference(getAssertedConstraintIds(), setA);

    return creator.encapsulateBoolean(
        interpolate(
            transformedImmutableSetCopy(setA, stack.peekLast()::get),
            transformedImmutableSetCopy(setB, stack.peekLast()::get)));
  }

  private int interpolate(Collection<Integer> setA, Collection<Integer> setB)
      throws InterruptedException, SolverException {
    try (var ctxA = newContext("mcsat");
        var ctxB = newContext("mcsat")) {

      ctxA.assertFormulas(Ints.toArray(setA));
      ctxB.assertFormulas(Ints.toArray(setB));
      var context = new InterpolationContext(ctxA, ctxB);

      // TODO How to abort this?
      // For now, let's just check before and after the call:
      shutdownNotifier.shutdownIfNecessary();
      Status status;
      try {
        status = context.check(DEFAULT_PARAMS, false);
      } catch (YicesException e) {
        if (ACCEPTED_INTERPOLATION_ERROR_MESSAGES.contains(e.getMessage())) {
          throw new SolverException(e.getMessage().stripTrailing());
        } else {
          throw e;
        }
      }
      shutdownNotifier.shutdownIfNecessary();
      if (status == Status.UNSAT) {
        return context.getInterpolant();
      } else {
        throw new IllegalStateException("Solver state must be unsat");
      }
    }
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<Integer>> partitions)
      throws SolverException, InterruptedException {
    final int n = partitions.size();
    final List<BooleanFormula> itps = new ArrayList<>();
    var previousItp = Terms.mkTrue();
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
