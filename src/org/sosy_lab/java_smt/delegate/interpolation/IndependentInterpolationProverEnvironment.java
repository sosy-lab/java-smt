/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.interpolation;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.delegate.interpolation.techniques.AbstractInterpolationTechnique;
import org.sosy_lab.java_smt.delegate.interpolation.techniques.ModelBasedProjectionInterpolation;
import org.sosy_lab.java_smt.delegate.interpolation.techniques.QuantifierEliminationInterpolation;

public class IndependentInterpolationProverEnvironment
    implements InterpolatingProverEnvironment<String> {
  private final SolverContext solverContext;
  private final ProverEnvironment delegate;

  private final AbstractInterpolationTechnique interpolationTechnique;

  private final FormulaManager mgr;
  private final BooleanFormulaManager bmgr;

  private static final String PREFIX = "javasmt_itp_term_"; // for term-names
  private static final UniqueIdGenerator termIdGenerator =
      new UniqueIdGenerator(); // for different term-names

  private final List<Multimap<BooleanFormula, String>> assertedFormulas = new ArrayList<>();

  private enum LastCheck {
    SAT,
    UNSAT,
    NONE
  }

  private LastCheck lastCheck = LastCheck.NONE;

  protected IndependentInterpolationProverEnvironment(
      SolverContext pSolverContext,
      IndependentInterpolationSolverContext.InterpolationMethod pInterpolationMethod,
      ProverEnvironment pDelegate) {
    solverContext = checkNotNull(pSolverContext);
    delegate = checkNotNull(pDelegate);

    mgr = pSolverContext.getFormulaManager();
    bmgr = mgr.getBooleanFormulaManager();

    switch (pInterpolationMethod) {
      case MODEL_PROJECTION ->
          interpolationTechnique = new ModelBasedProjectionInterpolation(solverContext);
      case QUANTIFIER_ELIMINATION_FORWARD ->
          interpolationTechnique =
              new QuantifierEliminationInterpolation(mgr, pInterpolationMethod);
      case QUANTIFIER_ELIMINATION_BACKWARD ->
          interpolationTechnique =
              new QuantifierEliminationInterpolation(mgr, pInterpolationMethod);
      default -> throw new AssertionError();
    }
    assertedFormulas.add(LinkedHashMultimap.create());
  }

  private static String generateTermName() {
    return PREFIX + termIdGenerator.getFreshId();
  }

  protected ImmutableSet<String> getAssertedConstraintIds() {
    ImmutableSet.Builder<String> builder = ImmutableSet.builder();
    for (Multimap<BooleanFormula, String> level : assertedFormulas) {
      builder.addAll(level.values());
    }
    return builder.build();
  }

  /** Provides the set of BooleanFormulas to interpolate on. */
  private record InterpolationGroups(
      Collection<BooleanFormula> formulasOfA, Collection<BooleanFormula> formulasOfB) {}

  /**
   * @param nativeFormulasOfA a group of formulas that has been asserted and is to be interpolated
   *     against.
   * @return The de-duplicated collection of the 2 interpolation groups currently asserted as {@link
   *     BooleanFormula}s.
   */
  private InterpolationGroups getInterpolationGroups(Collection<String> nativeFormulasOfA) {
    checkArgument(
        getAssertedConstraintIds().containsAll(nativeFormulasOfA),
        "interpolation can only be done over previously asserted formulas.");

    ImmutableSet.Builder<BooleanFormula> formulasOfA = ImmutableSet.builder();
    ImmutableSet.Builder<BooleanFormula> formulasOfB = ImmutableSet.builder();
    for (Multimap<BooleanFormula, String> assertedFormulasPerLevel : assertedFormulas) {
      for (Map.Entry<BooleanFormula, String> assertedFormulaAndItpPoint :
          assertedFormulasPerLevel.entries()) {
        if (nativeFormulasOfA.contains(assertedFormulaAndItpPoint.getValue())) {
          formulasOfA.add(assertedFormulaAndItpPoint.getKey());
        } else {
          formulasOfB.add(assertedFormulaAndItpPoint.getKey());
        }
      }
    }
    return new InterpolationGroups(formulasOfA.build(), formulasOfB.build());
  }

  @Override
  public BooleanFormula getInterpolant(Collection<String> identifiersForA)
      throws SolverException, InterruptedException {
    checkState(lastCheck == LastCheck.UNSAT);

    if (identifiersForA.isEmpty()) {
      return bmgr.makeTrue();
    }

    InterpolationGroups interpolationGroups = getInterpolationGroups(identifiersForA);
    Collection<BooleanFormula> formulasOfA = interpolationGroups.formulasOfA();
    Collection<BooleanFormula> formulasOfB = interpolationGroups.formulasOfB();

    if (formulasOfB.isEmpty()) {
      return bmgr.makeFalse();
    }

    BooleanFormula conjugatedFormulasOfA = bmgr.and(formulasOfA);
    BooleanFormula conjugatedFormulasOfB = bmgr.and(formulasOfB);

    if (bmgr.isFalse(conjugatedFormulasOfA)) {
      return bmgr.makeFalse();
    } else if (bmgr.isFalse(conjugatedFormulasOfB)) {
      return bmgr.makeTrue();
    }

    BooleanFormula interpolant =
        interpolationTechnique.getInterpolant(conjugatedFormulasOfA, conjugatedFormulasOfB);

    assert satisfiesInterpolationCriteria(
        interpolant, conjugatedFormulasOfA, conjugatedFormulasOfB);

    return interpolant;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<String>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException(
        "Tree interpolants are not supported for independent interpolation currently.");
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(
      List<? extends Collection<String>> pPartitionedFormulas)
      throws SolverException, InterruptedException {
    // TODO Add sequential interpolation
    throw new UnsupportedOperationException(
        "Sequential interpolants are not supported for independent interpolation currently.");
  }

  /**
   * Checks the following 3 criteria for Craig interpolants:
   *
   * <p>1. the implication A ⇒ interpolant holds,
   *
   * <p>2. the conjunction interpolant ∧ B is unsatisfiable, and
   *
   * <p>3. interpolant only contains symbols that occur in both A and B.
   */
  private boolean satisfiesInterpolationCriteria(
      BooleanFormula interpolant,
      BooleanFormula conjugatedFormulasOfA,
      BooleanFormula conjugatedFormulasOfB)
      throws InterruptedException, SolverException {

    // checks that every Symbol of the interpolant appears either in A or B
    Set<String> interpolantSymbols = mgr.extractVariablesAndUFs(interpolant).keySet();
    Set<String> interpolASymbols = mgr.extractVariablesAndUFs(conjugatedFormulasOfA).keySet();
    Set<String> interpolBSymbols = mgr.extractVariablesAndUFs(conjugatedFormulasOfB).keySet();
    Set<String> intersection = Sets.intersection(interpolASymbols, interpolBSymbols);
    checkState(
        intersection.containsAll(interpolantSymbols),
        "Interpolant contains symbols %s that are not part of both input formula groups A and B.",
        Sets.difference(interpolantSymbols, intersection));

    try (ProverEnvironment validationSolver = getDistinctProver()) {
      validationSolver.push();
      // A -> interpolant is SAT
      validationSolver.addConstraint(bmgr.implication(conjugatedFormulasOfA, interpolant));
      checkState(
          !validationSolver.isUnsat(),
          "Invalid Craig interpolation: formula group A does not imply the interpolant.");
      validationSolver.pop();

      validationSolver.push();
      // interpolant AND B is UNSAT
      validationSolver.addConstraint(bmgr.and(interpolant, conjugatedFormulasOfB));
      checkState(
          validationSolver.isUnsat(),
          "Invalid Craig interpolation: interpolant does not contradict formula group B.");
      validationSolver.pop();
    }
    return true;
  }

  /**
   * Create a new, distinct prover to interpolate on. Will be able to generate models.
   *
   * @return A new {@link ProverEnvironment} configured to generate models.
   */
  private ProverEnvironment getDistinctProver() {
    // TODO: we should include the possibility to choose from options here. E.g. CHC/Horn solvers.
    return solverContext.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS);
  }

  @Override
  public void pop() {
    delegate.pop();
    assertedFormulas.remove(assertedFormulas.size() - 1);
    lastCheck = LastCheck.NONE;
  }

  @Override
  public String addConstraint(BooleanFormula constraint) throws InterruptedException {
    String termName = generateTermName();
    delegate.addConstraint(constraint);
    Iterables.getLast(assertedFormulas).put(constraint, termName);
    lastCheck = LastCheck.NONE;
    return termName;
  }

  @Override
  public void push() throws InterruptedException {
    delegate.push();
    assertedFormulas.add(LinkedHashMultimap.create());
    lastCheck = LastCheck.NONE;
  }

  @Override
  public int size() {
    return delegate.size();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    boolean unsat = delegate.isUnsat();
    lastCheck = unsat ? LastCheck.UNSAT : LastCheck.SAT;
    return unsat;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    boolean unsat = delegate.isUnsatWithAssumptions(assumptions);
    lastCheck = unsat ? LastCheck.UNSAT : LastCheck.SAT;
    return unsat;
  }

  @Override
  public Model getModel() throws SolverException {
    return delegate.getModel();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    return delegate.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    return delegate.unsatCoreOverAssumptions(assumptions);
  }

  @Override
  public void close() {
    delegate.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    return delegate.allSat(callback, important);
  }
}
