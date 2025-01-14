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

  /**
   * Checks, whether an independent interpolation strategy is enabled for the given prover.
   *
   * @param pOptions A set of all enabled options for the prover to check.
   * @return {@code true} if an independent interpolation strategy is configured, {@code false}
   *     otherwise.
   */
  public static boolean hasIndependentInterpolationStrategy(Set<ProverOptions> pOptions) {
    return getIndependentInterpolationStrategy(pOptions) != null;
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

  @Override
  public BooleanFormula getInterpolant(Collection<TFormulaInfo> pFormulasOfA)
      throws SolverException, InterruptedException {
    checkArgument(
        super.getAssertedConstraintIds().containsAll(pFormulasOfA),
        "interpolation can only be done over previously asserted formulas.");

    if (interpolationStrategy == null) {
      if (delegate instanceof InterpolatingProverEnvironment) {
        // TODO: this case throws a ClassCastException
        // Use native solver interpolation
        // return ((InterpolatingProverEnvironment<TFormulaInfo>) delegate).getInterpolant
        // (pFormulasOfA);
      } else {
        throw new UnsupportedOperationException(
            "Solver does not natively support interpolation in JavaSMT currently.");
      }
    }

    InterpolationFormulas formulasAAndB = super.getInterpolationGroups(pFormulasOfA);
    Collection<BooleanFormula> formulasOfA = formulasAAndB.gotFormulasForA();
    Collection<BooleanFormula> formulasOfB = formulasAAndB.gotFormulasForB();

    Preconditions.checkNotNull(formulasOfA);
    Preconditions.checkNotNull(formulasOfB);
    Preconditions.checkNotNull(interpolationStrategy);

    if (interpolationStrategy.equals(ProverOptions.GENERATE_MODEL_BASED_INTERPOLANTS)) {
      return getModelBasedInterpolant(formulasOfA, formulasOfB);
    } else {
      return getQuantifierEliminationBasedInterpolant(formulasOfA, formulasOfB);
    }
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<TFormulaInfo>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException(
        "Tree interpolants are not supported for independent interpolation currently.");
  }

  /**
   * Computes Craig interpolants for a {@link Collection} of {@link BooleanFormula}s using the
   * model-based solver independent interpolation strategy.
   *
   * <p>This interpolation strategy takes two sets of {@link BooleanFormula}s, A and B, as input to
   * generate Craig interpolants, based on the following definition of Craig interpolation:
   *
   * <ol>
   *   <li>The implication (A -> Itp) is unsatisfiable.
   *   <li>The implication (Itp -> NOT B) is unsatisfiable.
   *   <li>The interpolant Itp only contains symbols that appear in both sets of formulas A and B.
   * </ol>
   *
   * <p>Additionally, the Craig interpolant is a satisfying assignment to the following Constrained
   * Horn Clause:
   *
   * <ul>
   *   <li>For all (a, c). (A(a, c) -> Itp(c))
   *   <li>For all (b, c). (Itp(c) -> NOT (B(b, c)))
   * </ul>
   *
   * <p>A solver checks, whether the definition of Craig interpolation is satisfied and generates a
   * model accordingly.
   *
   * <p>Please note, that this interpolation strategy is only usable for solvers supporting
   * quantified solving over the theories interpolated upon. The solver does not need to support
   * interpolation itself.
   *
   * @param formulasOfA A {@link Collection} of {@link BooleanFormula}s representing the set of A.
   * @param formulasOfB A {@link Collection} of {@link BooleanFormula}s representing the set of B.
   * @return the Craig interpolant, otherwise {@code false} in case an interpolant can not be found.
   * @see <a href="https://github.com/agurfinkel/spacer-on-jupyter/blob/master/Dagstuhl2019.ipynb">
   *     Binary Craig Interpolation by reduction to CHC</a>
   */
  private BooleanFormula getModelBasedInterpolant(
      Collection<BooleanFormula> formulasOfA, Collection<BooleanFormula> formulasOfB)
      throws InterruptedException, SolverException {

    ProverEnvironment itpProver = getDistinctProver();

    BooleanFormula conjugatedA = bmgr.and(formulasOfA);
    BooleanFormula conjugatedB = bmgr.and(formulasOfB);

    List<Formula> varsOfA = getVars(conjugatedA);
    List<Formula> varsOfB = getVars(conjugatedB);

    ImmutableList<Formula> sharedVars = getSharedVars(varsOfA, varsOfB);

    checkArgument(!varsOfA.isEmpty(),
        "The set of variables for formulas of A is empty and cannot be quantified.");
    checkArgument(!varsOfB.isEmpty(),
        "The set of variables for formulas of B is empty and cannot be quantified.");
    checkArgument(!sharedVars.isEmpty(),
        "The set of the shared variables is empty and cannot be quantified.");

    BooleanFormula itp = getUniqueInterpolant(sharedVars);
    BooleanFormula left = qfmgr.forall(varsOfA, bmgr.implication(conjugatedA, itp));
    BooleanFormula right = qfmgr.forall(varsOfB, bmgr.implication(itp, bmgr.not(conjugatedB)));

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
   * Computes uniform Craig interpolants for a {@link Collection} of {@link BooleanFormula}s using
   * the quantifier-based solver independent interpolation strategy with quantifier-elimination.
   *
   * <p>This interpolation strategy takes two sets of {@link BooleanFormula}s, A and B, as input and
   * their variables a, b, c, satisfying the following rules to generate uniform Craig interpolants,
   * a stronger version of Craig interpolants:
   *
   * <ul>
   *   <li>A set of variables a that appears in formulas of A, but not in formulas of B.
   *   <li>A set of variables b that appears in formulas of B, but not in formulas of A.
   *   <li>A set of variables c that appear in both sets of formulas A and B.
   * </ul>
   *
   * <p>Quantifier-elimination can be performed in two directions, forward and backward, to generate
   * uniform Craig interpolants:
   *
   * <ul>
   *   <li>Forward version: interpolation(A(a, c), B(b, c)) = exists a. A(a, c)
   *   <li>Backward version: interpolation(A(a, c), B(b, c)) = for all b. NOT B(b, c)
   * </ul>
   *
   * <p>A solver verifies, whether the definition of Craig interpolation is satisfied for the
   * resulting uniform Craig interpolant.
   *
   * <p>Please note, that this interpolation strategy is only usable for solver supporting
   * quantifier-elimination over theories interpolated upon. The solver does not need to support
   * interpolation itself.
   *
   * @param formulasOfA A {@link Collection} of {@link BooleanFormula}s representing the set of A.
   * @param formulasOfB A {@link Collection} of {@link BooleanFormula}s representing the set of B.
   * @return the uniform Craig interpolant, otherwise {@code false} in case an interpolant can not
   *     be found.
   */
  private BooleanFormula getQuantifierEliminationBasedInterpolant(
      Collection<BooleanFormula> formulasOfA, Collection<BooleanFormula> formulasOfB)
      throws SolverException, InterruptedException {

    BooleanFormula conjugatedA = bmgr.and(formulasOfA);
    BooleanFormula conjugatedB = bmgr.and(formulasOfB);

    ImmutableList<Formula> varsOfA = getVars(conjugatedA);
    ImmutableList<Formula> varsOfB = getVars(conjugatedB);

    ImmutableList<Formula> sharedVars = getSharedVars(varsOfA, varsOfB);

    checkArgument(!varsOfA.isEmpty(),
        "The set of variables for formulas of A is empty and cannot be quantified.");
    checkArgument(!varsOfB.isEmpty(),
        "The set of variables for formulas of B is empty and cannot be quantified.");
    checkArgument(!sharedVars.isEmpty(),
        "The set of the shared variables is empty and cannot be quantified.");

    Preconditions.checkState(isUnsat());
    checkNotNull(interpolationStrategy);

    BooleanFormula interpolant = bmgr.makeFalse();
    if (interpolationStrategy.equals(ProverOptions.GENERATE_UNIFORM_BACKWARD_INTERPOLANTS)) {
      interpolant = getBackwardInterpolant(conjugatedB, varsOfB, sharedVars);
    } else if (interpolationStrategy.equals(ProverOptions.GENERATE_UNIFORM_FORWARD_INTERPOLANTS)) {
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

    if (!boundVars.isEmpty()) {
      BooleanFormula forward = qfmgr.exists(boundVars, formulasOfA);
      return qfmgr.eliminateQuantifiers(forward);
    }

    // TODO: catch possible exception and rethrow with additional information about the context

    // TODO: check that the quantifier has been eliminated properly and return either false or an
    //  error if its still present!

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

    if (!boundVars.isEmpty()) {
      BooleanFormula backward = qfmgr.forall(boundVars, bmgr.not(formulasOfB));
      return qfmgr.eliminateQuantifiers(backward);
    }
    // TODO: catch possible exception and rethrow with additional information about the context

    // TODO: check that the quantifier has been eliminated properly and return either false or an
    //  error if its still present!

    return formulasOfB;
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
   * Identifies the bound variables in a formula. Variables are bound for uniform interpolation in a
   * quantified formula only if they are not shared between A and B.
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

    return boundVars;
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

  private ProverEnvironment getDistinctProver() {
    return solverContext.newProverEnvironment(ProverOptions.GENERATE_MODELS);
  }

  /**
   * Checks, whether the returned interpolant indeed satisfies Craig interpolation.
   *
   * @param itp The given interpolant to check if it satisfies the definition of Craig interpolants.
   * @param formulasOfA The set of formulas A, combined into one {@link BooleanFormula}.
   * @param formulasOfB The set of formulas B, combined into one {@link BooleanFormula}.
   * @param varsOfA A list of all variables in formulas of A.
   * @param varsOfB A list of all variables in formulas of B.
   * @return {@code true}, if the given interpolant is a valid Craig interpolant, returns {@code
   *     false} otherwise.
   */
  private boolean satisfiesInterpolationCriteria(
      BooleanFormula itp, BooleanFormula formulasOfA, BooleanFormula formulasOfB,
      List<Formula> varsOfA, List<Formula> varsOfB)
      throws SolverException, InterruptedException {

    boolean result = false;

    BooleanFormula left = qfmgr.forall(varsOfA, bmgr.implication(formulasOfA, itp));
    BooleanFormula right = qfmgr.forall(varsOfB, bmgr.implication(itp, bmgr.not(formulasOfB)));

    ProverEnvironment itpProver = getDistinctProver();
    itpProver.push(bmgr.and(left, right));

    if (!itpProver.isUnsat()) {
      result = true;
    }

    itpProver.close();
    return result;
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
