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
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Multimap;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

public abstract class AbstractProver<T> implements BasicProverEnvironment<T> {

  protected final boolean generateModels;
  protected final boolean generateAllSat;
  protected final boolean generateUnsatCores;
  private final boolean generateUnsatCoresOverAssumptions;
  protected final boolean enableSL;
  protected boolean closed = false;

  private final Set<Evaluator> evaluators = new LinkedHashSet<>();

  /**
   * This data-structure tracks all formulas that were asserted on different levels. We can assert a
   * formula multiple times on the same or also distinct levels and return a new ID for each
   * assertion.
   */
  private final List<Multimap<BooleanFormula, T>> assertedFormulas = new ArrayList<>();

  private static final String TEMPLATE = "Please set the prover option %s.";

  protected AbstractProver(Set<ProverOptions> pOptions) {
    generateModels = pOptions.contains(ProverOptions.GENERATE_MODELS);
    generateAllSat = pOptions.contains(ProverOptions.GENERATE_ALL_SAT);
    generateUnsatCores = pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE);
    generateUnsatCoresOverAssumptions =
        pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS);
    enableSL = pOptions.contains(ProverOptions.ENABLE_SEPARATION_LOGIC);

    assertedFormulas.add(LinkedHashMultimap.create());
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
  public final void push() throws InterruptedException {
    checkState(!closed);
    pushImpl();
    assertedFormulas.add(LinkedHashMultimap.create());
  }

  protected abstract void pushImpl() throws InterruptedException;

  @Override
  public final void pop() {
    checkState(!closed);
    checkState(assertedFormulas.size() > 1, "initial level must remain until close");
    assertedFormulas.remove(assertedFormulas.size() - 1); // remove last
    popImpl();
  }

  protected abstract void popImpl();

  @Override
  @CanIgnoreReturnValue
  public final @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    checkState(!closed);
    T t = addConstraintImpl(constraint);
    Iterables.getLast(assertedFormulas).put(constraint, t);
    return t;
  }

  protected abstract @Nullable T addConstraintImpl(BooleanFormula constraint)
      throws InterruptedException;

  protected ImmutableSet<BooleanFormula> getAssertedFormulas() {
    ImmutableSet.Builder<BooleanFormula> builder = ImmutableSet.builder();
    for (Multimap<BooleanFormula, T> level : assertedFormulas) {
      builder.addAll(level.keySet());
    }
    return builder.build();
  }

  /**
   * @param nativeFormulasOfA a group of formulas that has been asserted and is to be interpolated
   *     against.
   * @return The de-duplicated collection of the 2 interpolation groups currently asserted as {@link
   *     BooleanFormula}s.
   */
  protected InterpolationGroups getInterpolationGroups(Collection<T> nativeFormulasOfA) {
    ImmutableSet.Builder<BooleanFormula> formulasOfA = ImmutableSet.builder();
    ImmutableSet.Builder<BooleanFormula> formulasOfB = ImmutableSet.builder();
    for (Multimap<BooleanFormula, T> assertedFormulasPerLevel : assertedFormulas) {
      for (Entry<BooleanFormula, T> assertedFormulaAndItpPoint :
          assertedFormulasPerLevel.entries()) {
        if (nativeFormulasOfA.contains(assertedFormulaAndItpPoint.getValue())) {
          formulasOfA.add(assertedFormulaAndItpPoint.getKey());
        } else {
          formulasOfB.add(assertedFormulaAndItpPoint.getKey());
        }
      }
    }
    return InterpolationGroups.of(formulasOfA.build(), formulasOfB.build());
  }

  protected ImmutableSet<T> getAssertedConstraintIds() {
    ImmutableSet.Builder<T> builder = ImmutableSet.builder();
    for (Multimap<BooleanFormula, T> level : assertedFormulas) {
      builder.addAll(level.values());
    }
    return builder.build();
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
    ImmutableList.copyOf(evaluators).forEach(Evaluator::close);
    evaluators.clear();
  }

  @Override
  public void close() {
    assertedFormulas.clear();
    closeAllEvaluators();
    closed = true;
  }

  /** Provides the set of BooleanFormulas to interpolate on. */
  public static class InterpolationGroups {
    private final Collection<BooleanFormula> formulasOfA;
    private final Collection<BooleanFormula> formulasOfB;

    private InterpolationGroups(
        Collection<BooleanFormula> pFormulasOfA, Collection<BooleanFormula> pFormulasOfB) {
      Preconditions.checkNotNull(pFormulasOfA);
      Preconditions.checkNotNull(pFormulasOfB);
      formulasOfA = pFormulasOfA;
      formulasOfB = pFormulasOfB;
    }

    protected static InterpolationGroups of(
        Collection<BooleanFormula> pFormulasOfA, Collection<BooleanFormula> pFormulasOfB) {
      return new InterpolationGroups(pFormulasOfA, pFormulasOfB);
    }

    protected Collection<BooleanFormula> getFormulasOfA() {
      return formulasOfA;
    }

    protected Collection<BooleanFormula> getFormulasOfB() {
      return formulasOfB;
    }
  }
}
