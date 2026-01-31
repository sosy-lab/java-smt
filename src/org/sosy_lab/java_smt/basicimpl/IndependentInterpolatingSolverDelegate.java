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
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Sets;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

public class IndependentInterpolatingSolverDelegate<T> extends AbstractProver<T>
    implements InterpolatingProverEnvironment<T> {

  private final SolverContext solverContext;

  private final InterpolatingProverEnvironment<T> delegate;

  private final @Nullable ProverOptions interpolationStrategy;

  private final FormulaManager mgr;
  private final BooleanFormulaManager bmgr;
  private final UFManager ufmgr;

  private static final String PREFIX = "javasmt_itp_term_"; // for term-names
  private static final UniqueIdGenerator termIdGenerator =
      new UniqueIdGenerator(); // for different term-names

  Map<String, BooleanFormula> itpPointsMap = new HashMap<>();

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
    ufmgr = mgr.getUFManager();
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
    List<? extends Formula> variablesInA = getAllVariables(conjugatedFormulasOfA);
    List<? extends Formula> variablesInB = getAllVariables(conjugatedFormulasOfB);
    List<Formula> sharedVariables = getCommonFormulas(variablesInA, variablesInB);
    List<Formula> exclusiveVariablesInA = removeVariablesFrom(variablesInA, sharedVariables);
    List<Formula> exclusiveVariablesInB = removeVariablesFrom(variablesInB, sharedVariables);

    BooleanFormula interpolant;

    if (bmgr.isFalse(conjugatedFormulasOfA)) {
      return bmgr.makeFalse();
    } else if (bmgr.isFalse(conjugatedFormulasOfB)) {
      return bmgr.makeTrue();
    }

    if (interpolationStrategy == null) {
      interpolant = delegate.getInterpolant(identifiersForA);

    } else {
      switch (interpolationStrategy) {
        case GENERATE_PROJECTION_BASED_INTERPOLANTS:
          interpolant =
              getModelBasedProjectionInterpolant(
                  conjugatedFormulasOfA,
                  conjugatedFormulasOfB,
                  variablesInA,
                  variablesInB,
                  sharedVariables);
          break;
        case GENERATE_UNIFORM_FORWARD_INTERPOLANTS:
          // Will generate interpolants based on quantifier elimination
          if (exclusiveVariablesInA.isEmpty()) {
            return conjugatedFormulasOfA;
          }
          interpolant = getUniformForwardInterpolant(conjugatedFormulasOfA, exclusiveVariablesInA);
          break;
        case GENERATE_UNIFORM_BACKWARD_INTERPOLANTS:
          if (exclusiveVariablesInB.isEmpty()) {
            return bmgr.not(conjugatedFormulasOfB);
          }
          // Note: uses the A -> i -> B is valid definition for Craig-Interpolants, so we negate B
          interpolant = getUniformBackwardInterpolant(conjugatedFormulasOfB, exclusiveVariablesInB);
          break;
        default:
          throw new AssertionError("Unknown interpolation strategy.");
      }
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
   * Extracts all variables (not UFs) from the given formula. There are no duplicates in the list. *
   */
  private List<? extends Formula> getAllVariables(BooleanFormula formula) {
    return mgr.extractVariables(formula).values().asList();
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

  /** interpolate(A(x,y),B(y,z))=∀z.¬B(y,z). */
  private BooleanFormula getUniformBackwardInterpolant(
      BooleanFormula formulasOfB, List<Formula> exclusiveVariables)
      throws SolverException, InterruptedException {

    QuantifiedFormulaManager qfmgr = mgr.getQuantifiedFormulaManager();
    BooleanFormula itpBackwardQuantified = qfmgr.forall(exclusiveVariables, bmgr.not(formulasOfB));
    BooleanFormula itpBackward = qfmgr.eliminateQuantifiers(itpBackwardQuantified);
    // Check that the top-level quantifier has been eliminated
    if (isQuantifiedFormula(itpBackward)) {
      throw new SolverException(
          "Error when calculating uniform interpolant, quantifier elimination failed.");
    }

    return mgr.simplify(itpBackward);
  }

  /** Checks the formula for a quantifier at an arbitrary position/depth. */
  private boolean isQuantifiedFormula(BooleanFormula maybeQuantifiedFormula) {
    final AtomicBoolean isQuantified = new AtomicBoolean(false);
    mgr.visitRecursively(
        maybeQuantifiedFormula,
        new DefaultFormulaVisitor<>() {

          @Override
          protected TraversalProcess visitDefault(Formula pF) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitQuantifier(
              BooleanFormula pF,
              Quantifier pQ,
              List<Formula> pBoundVariables,
              BooleanFormula pBody) {
            isQuantified.set(true);
            return TraversalProcess.ABORT;
          }
        });
    return isQuantified.get();
  }

  /**
   * Computes the uniform Craig interpolant, utilizing quantifier-elimination in the forward
   * direction with: interpolate(A(x,y),B(y,z)) = ∃x.A(x,y)
   *
   * <p>Forward means, that the set of formulas A interpolates towards the set of formulas B.
   *
   * @param conjugatedFormulasOfA The set of formulas A, combined into one {@link BooleanFormula}.
   * @param exclusiveVariables A list of shared variables found in both sets of formulas A and B.
   * @return a uniform Craig interpolant or an exception is thrown.
   */
  private BooleanFormula getUniformForwardInterpolant(
      BooleanFormula conjugatedFormulasOfA, List<Formula> exclusiveVariables)
      throws SolverException, InterruptedException {

    QuantifiedFormulaManager qfmgr = mgr.getQuantifiedFormulaManager();
    BooleanFormula itpForwardQuantified = qfmgr.exists(exclusiveVariables, conjugatedFormulasOfA);
    BooleanFormula itpForward = qfmgr.eliminateQuantifiers(itpForwardQuantified);
    // Check that the top-level quantifier has been eliminated
    if (isQuantifiedFormula(itpForward)) {
      throw new SolverException(
          "Error when calculating uniform interpolant, quantifier elimination failed.");
    }

    return mgr.simplify(itpForward);
  }

  private BooleanFormula getModelBasedProjectionInterpolant(
      BooleanFormula conjugatedFormulasOfA,
      BooleanFormula conjugatedFormulasOfB,
      List<? extends Formula> variablesInA,
      List<? extends Formula> variablesInB,
      List<Formula> sharedVars)
      throws InterruptedException, SolverException {

    QuantifiedFormulaManager qfmgr = mgr.getQuantifiedFormulaManager();

    BooleanFormula itp =
        ufmgr.declareAndCallUF(
            "__itp_internal_javasmt_" + termIdGenerator.getFreshId(),
            FormulaType.BooleanType,
            sharedVars);
    BooleanFormula left;
    BooleanFormula right;
    if (variablesInA.isEmpty()) {
      left = bmgr.implication(conjugatedFormulasOfA, itp);
    } else {
      left = qfmgr.forall(variablesInA, bmgr.implication(conjugatedFormulasOfA, itp));
    }
    // BooleanFormula left = qfmgr.forall(variablesInA, bmgr.implication(conjugatedFormulasOfA,
    // itp));
    if (variablesInB.isEmpty()) {
      right = bmgr.implication(itp, bmgr.not(conjugatedFormulasOfB));
    } else {
      right = qfmgr.forall(variablesInB, bmgr.implication(itp, bmgr.not(conjugatedFormulasOfB)));
    }

    BooleanFormula interpolant = bmgr.makeFalse();
    try (ProverEnvironment itpProver = getDistinctProver()) {

      itpProver.push(left);
      itpProver.push(right);

      if (!itpProver.isUnsat()) {
        try (Model model = itpProver.getModel()) {
          interpolant = model.eval(itp);
        }
        checkNotNull(interpolant);
      }
    }
    return mgr.simplify(interpolant);
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

  /** Returns common {@link org.sosy_lab.java_smt.api.Formula}s of the 2 given lists. * */
  private List<Formula> getCommonFormulas(
      List<? extends Formula> variables1, List<? extends Formula> variables2) {
    Set<Formula> set = new LinkedHashSet<>(variables1);
    set.retainAll(variables2);
    return ImmutableList.copyOf(set);
  }

  /**
   * Removes variablesToRemove from variablesToRemoveFrom and returns a new list without modifying
   * the old lists.
   */
  private List<Formula> removeVariablesFrom(
      List<? extends Formula> variablesToRemoveFrom, List<? extends Formula> variablesToRemove) {
    ImmutableList.Builder<Formula> builder = ImmutableList.builder();
    for (Formula var : variablesToRemoveFrom) {
      if (!variablesToRemove.contains(var)) {
        builder.add(var);
      }
    }
    return builder.build();
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
  public boolean isUnsat() throws SolverException, InterruptedException {
    return delegate.isUnsat();
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
