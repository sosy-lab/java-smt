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
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
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
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UFManager;

// The non-interpolating delegates usually return nothing useful as itp points, so we have to
// track it here
@SuppressWarnings("unused")
public class IndependentInterpolatingProverEnvironment<TFormulaInfo, TType>
    extends AbstractProver<TFormulaInfo> implements InterpolatingProverEnvironment<TFormulaInfo> {

  // TODO: use context to create distinct provers to interpolate on (formulas needs to be
  //  translated to and from that other instance!)
  private final SolverContext solverContext;
  private final ShutdownNotifier shutdownNotifier;
  private final ProverEnvironment delegate;

  private final FormulaCreator<TFormulaInfo, TType, ?, ?> creator;
  private final FormulaManager mgr;
  private final BooleanFormulaManager bmgr;
  private final UFManager ufmgr;
  private final QuantifiedFormulaManager qfmgr;

  // null for native solver interpolation
  private final @Nullable ProverOptions interpolationStrategy;

  private static final UniqueIdGenerator UNIQUE_ID_GENERATOR = new UniqueIdGenerator();
  private static final String PREFIX = "__internal_model_itp_generation_";

  public IndependentInterpolatingProverEnvironment(
      SolverContext sourceContext,
      FormulaCreator<TFormulaInfo, TType, ?, ?> pCreator,
      ProverEnvironment pDelegate,
      Set<ProverOptions> pOptions,
      ShutdownNotifier pShutdownNotifier) {
    super(pOptions);
    solverContext = checkNotNull(sourceContext);
    delegate = checkNotNull(pDelegate);
    creator = pCreator;
    shutdownNotifier = pShutdownNotifier;
    interpolationStrategy = getIndependentInterpolationStrategy(pOptions);
    mgr = sourceContext.getFormulaManager();
    bmgr = mgr.getBooleanFormulaManager();
    ufmgr = mgr.getUFManager();
    qfmgr = mgr.getQuantifiedFormulaManager();
  }

  private static @Nullable ProverOptions getIndependentInterpolationStrategy(
      Set<ProverOptions> pOptions) {
    List<ProverOptions> itpStrat = new ArrayList<>(pOptions);
    final Set<ProverOptions> allIndependentInterpolationStrategies =
        ImmutableSet.of(
            ProverOptions.GENERATE_MODEL_BASED_INTERPOLANTS,
            ProverOptions.GENERATE_UNIFORM_BACKWARD_INTERPOLANTS,
            ProverOptions.GENERATE_UNIFORM_FORWARD_INTERPOLANTS);
    itpStrat.retainAll(allIndependentInterpolationStrategies);
    if (itpStrat.isEmpty()) {
      return null;
    }
    Preconditions.checkState(itpStrat.size() == 1);
    return itpStrat.get(0);
  }

  public static boolean hasIndependentInterpolationStrategy(Set<ProverOptions> pOptions) {
    return getIndependentInterpolationStrategy(pOptions) != null;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<TFormulaInfo> pFormulasOfA)
      throws SolverException, InterruptedException {
    checkArgument(
        super.getAssertedConstraintIds().containsAll(pFormulasOfA),
        "interpolation can only be done over previously asserted formulas.");

    if (interpolationStrategy == null) {
      if (delegate instanceof InterpolatingProverEnvironment) {
        // TODO: this case
        // Use native solver interpolation
        // return ((InterpolatingProverEnvironment<TFormulaInfo>) delegate).getInterpolant
        // (pFormulasOfA);
      } else {
        throw new UnsupportedOperationException();
      }
    }

    InterpolationFormulas formulasAAndB = super.getInterpolationGroups(pFormulasOfA);
    Collection<BooleanFormula> formulasOfA = formulasAAndB.gotFormulasForA();
    Collection<BooleanFormula> formulasOfB = formulasAAndB.gotFormulasForB();

    if (interpolationStrategy.equals(ProverOptions.GENERATE_MODEL_BASED_INTERPOLANTS)) {
      return computeModelBasedInterpolant(formulasOfA, formulasOfB);
    } else {
      return getQuantifierEliminationBasedInterpolant(formulasOfA, formulasOfB);
    }
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<TFormulaInfo>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException(
        "TreeInterpolants are not supported for independent " + "interpolation currently.");
  }

  /**
   * Computes Craig interpolants for a pair of formulas using a model-based approach.
   *
   * <p>The model-based approach takes two groups of Boolean formulas, A and B, as input and returns
   * an interpolant Itp. The interpolant Itp satisfies the definition of Craig interpolation,
   * meaning:
   *
   * <ol>
   *   <li>(A -> Itp) is unsatisfiable,
   *   <li>(Itp -> not B) is unsatisfiable, and
   *   <li>Itp only contains symbols that appear in both formulas A and B.
   * </ol>
   *
   * <p>The variables shared between A and B are used to define the interpolant Itp, ensuring Itp
   * depends only on shared symbols. The constraints are created and checked for satisfiability:
   *
   * <ol>
   *   <li>For all (a, c). (A(a, c) -> Itp(c)), and
   *   <li>For all (b, c). (Itp(c) -> not (B(b, c))).
   * </ol>
   *
   * @param pFormulasOfA A Collection of Boolean formulas of A.
   * @param pFormulasOfB A Collection of Boolean formulas of B.
   * @return the Craig interpolant Itp if it satisfies the conditions, otherwise returns false.
   */
  private BooleanFormula computeModelBasedInterpolant(
      Collection<BooleanFormula> pFormulasOfA, Collection<BooleanFormula> pFormulasOfB)
      throws InterruptedException, SolverException {

    ProverEnvironment itpProver = getDistinctProver();

    BooleanFormula formulasOfA = bmgr.and(pFormulasOfA);
    BooleanFormula formulasOfB = bmgr.and(pFormulasOfB);

    List<Formula> varsOfA = getVars(formulasOfA);
    List<Formula> varsOfB = getVars(formulasOfB);

    ImmutableList<Formula> sharedVars = getSharedVars(varsOfA, varsOfB);

    BooleanFormula itp = getUniqueInterpolant(sharedVars);
    BooleanFormula left = qfmgr.forall(varsOfA, bmgr.implication(formulasOfA, itp));
    BooleanFormula right = qfmgr.forall(varsOfB, bmgr.implication(itp, bmgr.not(formulasOfB)));

    // check the satisfiability of the constraints and generate a model if possible
    itpProver.push(bmgr.and(left, right));

    BooleanFormula interpolant = bmgr.makeFalse();
    if (!itpProver.isUnsat()) {
      interpolant = itpProver.getModel().eval(itp);
      Preconditions.checkNotNull(interpolant);
    }

    itpProver.close();
    return interpolant;
  }

  /**
   * Computes uniform interpolants for a {@link Collection} of {@link BooleanFormula} using the
   * quantifier-based interpolation strategy with quantifier elimination (QE).
   *
   * <p>This approach generates an interpolant Itp for two sets of constraints A and B, where the
   * variables are categorized as follows:
   *
   * <ul>
   *   <li>Variables that appear only in formulas of A.
   *   <li>Variables that appear only in formulas of B.
   *   <li>Shared variables that appear in both sets of formulas A and B.
   * </ul>
   *
   * <p>The resulting Uniform Interpolant is a stronger version of a Craig Interpolant and satisfies
   * the definition of Craig Interpolation:
   *
   * <ol>
   *   <li>(A -> Itp) is unsatisfiable,
   *   <li>(Itp -> not B) is unsatisfiable, and
   *   <li>Itp only contains symbols that appear in both sets of formulas A and B.
   * </ol>
   *
   * @param formulasOfA A collection of {@link BooleanFormula}s representing the set A.
   * @param formulasOfB A collection of {@link BooleanFormula}s representing the set B.
   * @return the uniform Craig-Interpolant, returns false in case an interpolant can not be found.
   */
  private BooleanFormula getQuantifierEliminationBasedInterpolant(
      Collection<BooleanFormula> formulasOfA, Collection<BooleanFormula> formulasOfB)
      throws SolverException, InterruptedException {

    ProverEnvironment itpProver = getDistinctProver();

    BooleanFormula conjugatedA = bmgr.and(formulasOfA);
    BooleanFormula conjugatedB = bmgr.and(formulasOfB);

    ImmutableList<Formula> varsOfA = getVars(conjugatedA);
    ImmutableList<Formula> varsOfB = getVars(conjugatedB);

    ImmutableList<Formula> sharedVars = getSharedVars(varsOfA, varsOfB);

    BooleanFormula interpolant;
    if (interpolationStrategy.equals(ProverOptions.GENERATE_UNIFORM_BACKWARD_INTERPOLANTS)) {
      interpolant = getBackwardInterpolant(conjugatedB, varsOfB, sharedVars);
    } else {
      Preconditions.checkState(
          interpolationStrategy.equals(ProverOptions.GENERATE_UNIFORM_FORWARD_INTERPOLANTS));
      interpolant = getForwardInterpolant(conjugatedA, varsOfA, sharedVars);
    }

    return interpolant;
  }

  /**
   * Computes the forward interpolant for a given formula A. In the forward direction, the variables
   * specific to formula A are existentially quantified to describe the relationship between
   * formulas A and B.
   *
   * @param formulasOfA The {@link BooleanFormula} representing the constraints in formula A.
   * @param varsOfA The list of all variables in formula A.
   * @param sharedVars The list of shared variables between formulas A and B.
   * @return The forward interpolant.
   */
  private BooleanFormula getForwardInterpolant(
      BooleanFormula formulasOfA, List<Formula> varsOfA, List<Formula> sharedVars)
      throws SolverException, InterruptedException {

    ImmutableList<Formula> boundVars = getBoundVars(varsOfA, sharedVars);

    if (!boundVars.equals(sharedVars)) {
      BooleanFormula forward = qfmgr.exists(boundVars, formulasOfA);
      return qfmgr.eliminateQuantifiers(forward);
    }

    return formulasOfA;
  }

  /**
   * Computes the backward interpolant for a given formula B. In the backward direction, the
   * variables specific to formula B are universally quantified and formula B is negated to describe
   * the relationship between formulas A and B.
   *
   * @param formulasOfB The {@link BooleanFormula} representing the constraints in formula B.
   * @param varsOfB The list of all variables in formula B.
   * @param sharedVars The list of shared variables between formulas A and B.
   * @return The backward interpolant.
   */
  private BooleanFormula getBackwardInterpolant(
      BooleanFormula formulasOfB, List<Formula> varsOfB, List<Formula> sharedVars)
      throws SolverException, InterruptedException {

    ImmutableList<Formula> boundVars = getBoundVars(varsOfB, sharedVars);

    if (!boundVars.equals(sharedVars)) {
      BooleanFormula backward = qfmgr.forall(boundVars, bmgr.not(formulasOfB));
      return qfmgr.eliminateQuantifiers(backward);
    }

    return formulasOfB;
  }

  private ProverEnvironment getDistinctProver() {
    return solverContext.newProverEnvironment(ProverOptions.GENERATE_MODELS);
  }

  /**
   * Extracts all variables from the given {@link BooleanFormula}.
   *
   * @param formulas The formula from which to extract all variables.
   * @return An immutable list of all variables in the formula.
   */
  private ImmutableList<Formula> getVars(BooleanFormula formulas) {
    return ImmutableList.copyOf(mgr.extractVariablesAndUFs(formulas).values());
  }

  /**
   * Identifies the shared variables between two formulas A and B.
   *
   * @param varsOfA The list of variables from formula A.
   * @param varsOfB The list of variables from formula B.
   * @return An immutable list of variables found in both formulas A and B.
   */
  private ImmutableList<Formula> getSharedVars(List<Formula> varsOfA, List<Formula> varsOfB) {
    return varsOfA.stream().filter(varsOfB::contains).collect(ImmutableList.toImmutableList());
  }

  /**
   * Identifies the bound variables in a formula.
   *
   * @param vars The list of all variables in the formula to identify the bound ones.
   * @param sharedVars The shared variables between formulas A and B.
   * @return An immutable list of bound variables from a formula.
   */
  private ImmutableList<Formula> getBoundVars(List<Formula> vars, List<Formula> sharedVars) {
    ImmutableList<Formula> boundVars =
        vars.stream()
            .filter(var -> !sharedVars.contains(var))
            .collect(ImmutableList.toImmutableList());

    return boundVars.isEmpty() ? ImmutableList.copyOf(vars) : boundVars;
  }

  /**
   * Creates an interpolant with a unique identifier that satisfies the third definition of a Craig
   * Interpolant: its uninterpreted symbols are those shared between formulas A and B. This is used
   * as part of the model-based interpolation strategy to generate the final Craig Interpolant.
   *
   * @param sharedVars The shared variables between formulas A and B.
   * @return An interpolant whose uninterpreted symbols are those shared between formulas A and B.
   */
  private BooleanFormula getUniqueInterpolant(ImmutableList<Formula> sharedVars) {
    return ufmgr.declareAndCallUF(
        PREFIX + UNIQUE_ID_GENERATOR.getFreshId(), FormulaType.BooleanType, sharedVars);
  }

  /**
   * Removes all formulas currently asserted in the stack to reset it. This method is used, e.g.,
   * for a new check, such as verifying the satisfiability of a formula without considering
   * previously asserted formulas.
   */
  private void clearStack() {
    for (int i = 0; i < size(); i++) {
      pop();
    }
  }

  /**
   * Restores the solver's stack to its previous state before it was cleared by re-adding the
   * formulas that were removed, assuming the stack is currently empty.
   *
   * @param assertedFormulas The list of {@link BooleanFormula} to push back onto the stack.
   */
  private void restoreStack(List<BooleanFormula> assertedFormulas) throws InterruptedException {
    for (BooleanFormula formula : assertedFormulas) {
      push(formula);
    }
  }

  @Override
  protected void popImpl() {
    delegate.pop();
  }

  @Override
  protected @Nullable TFormulaInfo addConstraintImpl(BooleanFormula constraint)
      throws InterruptedException {
    checkState(!closed);
    TFormulaInfo t = creator.extractInfo(constraint);
    delegate.addConstraint(constraint);
    return t;
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
