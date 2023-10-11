// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkState;

import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.utils.Generator;

public abstract class AbstractProver<T> implements BasicProverEnvironment<T> {

  private final boolean generateModels;
  private final boolean generateAllSat;
  protected final boolean generateUnsatCores;
  private final boolean generateUnsatCoresOverAssumptions;
  protected final boolean enableSL;
  protected boolean closed = false;

  private final Set<Evaluator> evaluators = new LinkedHashSet<>();

  /** This data-structure tracks all formulas that were asserted on different levels. */
  private final List<Collection<BooleanFormula>> assertedFormulas = new ArrayList<>();

  private static final String TEMPLATE = "Please set the prover option %s.";

  protected AbstractProver(Set<ProverOptions> pOptions) {
    generateModels = pOptions.contains(ProverOptions.GENERATE_MODELS);
    generateAllSat = pOptions.contains(ProverOptions.GENERATE_ALL_SAT);
    generateUnsatCores = pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE);
    generateUnsatCoresOverAssumptions =
        pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
    enableSL = pOptions.contains(ProverOptions.ENABLE_SEPARATION_LOGIC);

    assertedFormulas.add(new LinkedHashSet<>());
  }

  protected final void checkGenerateModels() {
    Preconditions.checkState(generateModels, TEMPLATE, ProverOptions.GENERATE_MODELS);
  }

  protected final void checkGenerateAllSat() {
    Preconditions.checkState(generateAllSat, TEMPLATE, ProverOptions.GENERATE_ALL_SAT);
  }

  protected final void checkGenerateUnsatCores() {
    Preconditions.checkState(generateUnsatCores, TEMPLATE, ProverOptions.GENERATE_UNSAT_CORE);
  }

  protected final void checkGenerateUnsatCoresOverAssumptions() {
    Preconditions.checkState(
        generateUnsatCoresOverAssumptions,
        TEMPLATE,
        ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
  }

  protected final void checkEnableSeparationLogic() {
    Preconditions.checkState(enableSL, TEMPLATE, ProverOptions.ENABLE_SEPARATION_LOGIC);
  }

  @Override
  public int size() {
    checkState(!closed);
    return assertedFormulas.size() - 1;
  }

  @Override
  public void push() throws InterruptedException {
    checkState(!closed);
    assertedFormulas.add(new LinkedHashSet<>());
  }

  @Override
  public void pop() {
    checkState(!closed);
    checkState(assertedFormulas.size() > 1, "initial level must remain until close");
    assertedFormulas.remove(assertedFormulas.size() - 1); // remove last
  }

  @Override
  @CanIgnoreReturnValue
  public @Nullable T addConstraint(BooleanFormula constraint)
      throws InterruptedException {
    checkState(!closed);
    Iterables.getLast(assertedFormulas).add(constraint);
    Generator.logAddConstraint(constraint);
    return null;
  }

  protected ImmutableSet<BooleanFormula> getAssertedFormulas() {
    return FluentIterable.concat(assertedFormulas).toSet();
  }

  /**
   * This method registers the Evaluator to be cleaned up before the next change on the prover
   * stack.
   */
  protected <E extends Evaluator> E registerEvaluator(E pEvaluator) {
    evaluators.add(pEvaluator);
    return pEvaluator;
  }

  protected void unregisterEvaluator(Evaluator pEvaluator) {
    evaluators.remove(pEvaluator);
  }

  protected void closeAllEvaluators() {
    evaluators.forEach(Evaluator::close);
    evaluators.clear();
  }

  @Override
  public void close() {
    assertedFormulas.clear();
    closeAllEvaluators();
    closed = true;
  }
}
