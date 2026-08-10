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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import com.google.common.primitives.Ints;
import com.sri.yices.Context;
import com.sri.yices.InterpolationContext;
import com.sri.yices.Status;
import com.sri.yices.Terms;
import com.sri.yices.YicesException;
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
import org.sosy_lab.java_smt.basicimpl.ShutdownHook;

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

    try (var ctxA = newContext("mcsat");
        var ctxB = newContext("dpllt")) {

      ctxA.assertFormulas(Ints.toArray(transformedImmutableSetCopy(setA, stack.peekLast()::get)));
      try {
        ctxB.assertFormulas(Ints.toArray(transformedImmutableSetCopy(setB, stack.peekLast()::get)));
        ctxB.push(); // Will trigger an exception if B is already unsat by itself

      } catch (YicesException ye) {
        return creator.encapsulateBoolean(Terms.mkTrue());
      }
      return creator.encapsulateBoolean(interpolate(ctxA, ctxB));
    }
  }

  @SuppressWarnings("try")
  private int interpolate(Context ctxA, Context ctxB) throws InterruptedException, SolverException {
    var context = new InterpolationContext(ctxA, ctxB);

    Status status;
    try (ShutdownHook hook =
        new ShutdownHook(
            shutdownNotifier,
            () -> {
              ctxA.stopSearch();
              ctxB.stopSearch();
            })) {
      shutdownNotifier.shutdownIfNecessary();
      try {
        status = context.check(DEFAULT_PARAMS, false);
      } catch (YicesException e) {
        if (ACCEPTED_INTERPOLATION_ERROR_MESSAGES.contains(e.getMessage())) {
          throw new SolverException(e.getMessage().stripTrailing());
        } else {
          throw e;
        }
      }
    }

    switch (status) {
      case INTERRUPTED -> throw new InterruptedException();
      case UNSAT -> {
        return context.getInterpolant();
      }
      case UNKNOWN -> throw new SolverException("Could not interpolate");
      default -> throw new RuntimeException("Inconsistent SAT result during interpolation");
    }
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<Integer>> partitions)
      throws SolverException, InterruptedException {

    var groups =
        partitions.stream()
            .map(partition -> partition.stream().map(stack.peekLast()::get).toList())
            .toList();

    try (var ctxA = newContext("mcsat");
        var ctxB = newContext("dpllt")) {

      ctxB.push();
      int skipped = 0;
      for (int i = groups.size() - 1; i > 0; i--) {
        try {
          ctxB.assertFormulas(groups.get(i));
          ctxB.push();
        } catch (YicesException e) {
          // Yices will throw this exception once the Bs have become unsat
          skipped = i;
          break;
        }
      }
      ctxB.pop();

      ImmutableList.Builder<BooleanFormula> builder = ImmutableList.builder();

      var lastItp = Terms.mkTrue();
      for (int i = 0; i < groups.size() - 1; i++) {
        if (i < skipped) {
          // Interpolants are 'true' until B is no longer unsat by itself
          builder.add(creator.encapsulateBoolean(lastItp));

        } else {
          ctxA.push();

          ctxA.assertFormula(lastItp);
          ctxA.assertFormulas(groups.get(i));

          lastItp = interpolate(ctxA, ctxB);
          builder.add(creator.encapsulateBoolean(lastItp));

          ctxA.pop();
          ctxB.pop();
        }
      }

      return builder.build();
    }
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }
}
