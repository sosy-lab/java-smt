/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.base.Preconditions;
import com.google.common.collect.Sets;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.basicimpl.interpolation_techniques.AbstractInterpolationTechnique;
import org.sosy_lab.java_smt.basicimpl.interpolation_techniques.ModelBasedProjectionInterpolation;
import org.sosy_lab.java_smt.basicimpl.interpolation_techniques.QuantifierEliminationInterpolation;

public class IndependentInterpolatingSolverDelegate<T> extends AbstractProver<T>
    implements InterpolatingProverEnvironment<T> {

  private final SolverContext solverContext;

  private final InterpolatingProverEnvironment<T> delegate;

  private final @Nullable AbstractInterpolationTechnique interpolationTechnique;

  private final @Nullable ProverOptions interpolationStrategy;

  private final FormulaManager mgr;
  private final BooleanFormulaManager bmgr;

  private static final String PREFIX = "javasmt_itp_term_"; // for term-names
  private static final UniqueIdGenerator termIdGenerator =
      new UniqueIdGenerator(); // for different term-names

  protected IndependentInterpolatingSolverDelegate(
      AbstractSolverContext pSourceContext,
      InterpolatingProverEnvironment<T> pDelegate,
      Set<ProverOptions> pOptions) {
    super(checkNotNull(pOptions));
    solverContext = checkNotNull(pSourceContext);
    delegate = checkNotNull(pDelegate);
    interpolationStrategy = pSourceContext.getIndependentInterpolationStrategy(pOptions);
    mgr = pSourceContext.getFormulaManager();
    bmgr = mgr.getBooleanFormulaManager();

    if (interpolationStrategy == null) {
      this.interpolationTechnique = null;
    } else {
      switch (interpolationStrategy) {
        case GENERATE_PROJECTION_BASED_INTERPOLANTS:
          this.interpolationTechnique = new ModelBasedProjectionInterpolation(solverContext);
          break;
        case GENERATE_UNIFORM_FORWARD_INTERPOLANTS:
        case GENERATE_UNIFORM_BACKWARD_INTERPOLANTS:
          this.interpolationTechnique =
              new QuantifierEliminationInterpolation(mgr, interpolationStrategy);
          break;
        default:
          throw new AssertionError("Unknown interpolation strategy: " + interpolationStrategy);
      }
    }
  }

  // TODO: also present in SMTInterpol, generalize
  protected static String generateTermName() {
    return PREFIX + termIdGenerator.getFreshId();
  }

  @Override
  public BooleanFormula getInterpolant(Collection<T> identifiersForA)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    checkArgument(
        getAssertedConstraintIds().containsAll(identifiersForA),
        "Interpolation can only be performed over previously asserted formulas.");

    if (identifiersForA.isEmpty()) {
      return bmgr.makeTrue();
    }

    InterpolationGroups interpolationGroups = super.getInterpolationGroups(identifiersForA);
    Collection<BooleanFormula> formulasOfA = interpolationGroups.getFormulasOfA();
    Collection<BooleanFormula> formulasOfB = interpolationGroups.getFormulasOfB();

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

    BooleanFormula interpolant;

    if (interpolationTechnique == null) {
      interpolant = delegate.getInterpolant(identifiersForA);
    } else {
      interpolant =
          interpolationTechnique.getInterpolant(conjugatedFormulasOfA, conjugatedFormulasOfB);
    }

    assert satisfiesInterpolationCriteria(
        interpolant, conjugatedFormulasOfA, conjugatedFormulasOfB);

    return interpolant;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<T>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    if (interpolationStrategy == null) {
      // Use native solver interpolation
      return delegate.getTreeInterpolants(partitionedFormulas, startOfSubTree);
    }
    throw new UnsupportedOperationException(
        "Tree interpolants are not supported for independent interpolation currently.");
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<T>> pPartitionedFormulas)
      throws SolverException, InterruptedException {
    if (interpolationStrategy == null) {
      // Use native solver interpolation
      return delegate.getSeqInterpolants(pPartitionedFormulas);
    }
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
    return solverContext.newProverEnvironment(ProverOptions.GENERATE_MODELS);
  }

  @Override
  protected void popImpl() {
    delegate.pop();
  }

  @Override
  protected T addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    return delegate.addConstraint(constraint);
  }

  @Override
  protected void pushImpl() throws InterruptedException {
    delegate.push();
  }

  @Override
  public int size() {
    return delegate.size();
  }

  @Override
  public boolean isUnsatImpl() throws SolverException, InterruptedException {
    return delegate.isUnsat();
  }

  @Override
  public boolean hasPersistentModel() {
    return false;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    return delegate.isUnsatWithAssumptions(assumptions);
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
