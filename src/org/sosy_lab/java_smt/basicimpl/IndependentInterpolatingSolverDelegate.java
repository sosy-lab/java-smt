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

import static com.google.common.base.Preconditions.checkNotNull;
import static org.sosy_lab.java_smt.test.BooleanFormulaSubject.assertUsing;

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
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
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

    // TODO: refactor the selection of interpolationTechnique by introducing a method for it
    if (interpolationStrategy == null) {
      interpolationTechnique = null;
    } else {
      interpolationTechnique =
          switch (interpolationStrategy) {
            case GENERATE_PROJECTION_BASED_INTERPOLANTS ->
                new ModelBasedProjectionInterpolation(solverContext);
            case GENERATE_UNIFORM_FORWARD_INTERPOLANTS, GENERATE_UNIFORM_BACKWARD_INTERPOLANTS ->
                new QuantifierEliminationInterpolation(mgr, interpolationStrategy);
            default ->
                throw new AssertionError(
                    "Unknown interpolation strategy: " + interpolationStrategy);
          };
    }
  }

  // TODO: also present in SMTInterpol, generalize
  protected static String generateTermName() {
    return PREFIX + termIdGenerator.getFreshId();
  }

  /** Check if assertions are enabled. */
  private boolean areAssertionsEnabled() {
    try {
      assert false;
    } catch (AssertionError e) {
      return true;
    }
    return false;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<T> identifiersForA)
      throws SolverException, InterruptedException {

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

    BooleanFormula interpolant;

    if (interpolationTechnique == null) {
      interpolant = delegate.getInterpolant(identifiersForA);
    } else {
      if (bmgr.isFalse(conjugatedFormulasOfA)) {
        return bmgr.makeFalse();
      } else if (bmgr.isFalse(conjugatedFormulasOfB)) {
        return bmgr.makeTrue();
      }

      interpolant =
          interpolationTechnique.getInterpolant(conjugatedFormulasOfA, conjugatedFormulasOfB);
    }

    if (areAssertionsEnabled()) {
      // Only validate interpolants when assertions are enabled as this is an expensive check
      assertUsing(solverContext)
          .that(interpolant)
          .isValidInterpolant(conjugatedFormulasOfA, conjugatedFormulasOfB);
    }

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
  protected Model getModelImpl() throws SolverException {
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
