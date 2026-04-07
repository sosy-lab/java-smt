/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.FluentIterable;
import com.google.common.collect.Iterables;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Option;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Options;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Vector_Term;

class BitwuzlaInterpolatingProver extends BitwuzlaAbstractProver<Integer>
    implements InterpolatingProverEnvironment<Integer> {

  BitwuzlaInterpolatingProver(
      BitwuzlaFormulaManager pManager,
      BitwuzlaFormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions,
      Options pSolverOptions) {
    super(pManager, pCreator, pShutdownNotifier, pOptions, enableInterpolation(pSolverOptions));
  }

  private static Options enableInterpolation(Options pSolverOptions) {
    Options newOptions = new Options(pSolverOptions);
    newOptions.set(Option.PRODUCE_INTERPOLANTS, 1);
    return newOptions;
  }

  @Override
  protected @Nullable Integer addConstraintImpl(BooleanFormula constraint)
      throws InterruptedException {
    return addConstraint0(constraint);
  }

  @Override
  public BooleanFormula getInterpolant(Collection<Integer> formulasOfA)
      throws SolverException, InterruptedException {
    return creator.encapsulateBoolean(
        formulasOfA.isEmpty()
            ? creator.getEnv().mk_true()
            : env.get_interpolant(
                new Vector_Term(FluentIterable.from(formulasOfA).transform(stack.peek()::get))));
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas)
      throws SolverException, InterruptedException {

    Vector_Vector_Term partitions =
        new Vector_Vector_Term(
            FluentIterable.from(partitionedFormulas)
                .transform(
                    p -> new Vector_Term(FluentIterable.from(p).transform(stack.peek()::get))));
    Vector_Term itps = env.get_interpolants(partitions);
    checkState(
        creator.getEnv().mk_false().equals(Iterables.getLast(itps)),
        "the last interpolant should be false");
    return FluentIterable.from(itps)
        .limit(itps.size() - 1) // ignore the last interpolant, which is always "false"
        .transform(creator::encapsulateBoolean)
        .toList();
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Bitwuzla does not support tree interpolation");
  }
}
