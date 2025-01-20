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
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
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

  private final SolverContext solverContext;
  private final ShutdownNotifier shutdownNotifier;
  private final BasicProverEnvironment<?> delegate;

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
      SolverContext pSourceContext,
      FormulaCreator<TFormulaInfo, TType, ?, ?> pCreator,
      BasicProverEnvironment<?> pDelegate,
      Set<ProverOptions> pOptions,
      ShutdownNotifier pShutdownNotifier) {
    super(pOptions);
    solverContext = checkNotNull(pSourceContext);
    delegate = checkNotNull(pDelegate);
    creator = pCreator;
    shutdownNotifier = pShutdownNotifier;
    interpolationStrategy = getIndependentInterpolationStrategy(pOptions);
    mgr = pSourceContext.getFormulaManager();
    bmgr = mgr.getBooleanFormulaManager();
    ufmgr = mgr.getUFManager();
    qfmgr = mgr.getQuantifiedFormulaManager();
  }

  /**
   * Checks, whether an independent interpolation strategy is enabled for the given prover.
   *
   * @param options A set of all enabled options for the prover to check.
   * @return {@code true} if an independent interpolation strategy is configured, {@code false}
   *     otherwise.
   */
  public static boolean hasIndependentInterpolationStrategy(Set<ProverOptions> options) {
    return getIndependentInterpolationStrategy(options) != null;
  }

  private static @Nullable ProverOptions getIndependentInterpolationStrategy(
      Set<ProverOptions> options) {
    List<ProverOptions> itpStrat = new ArrayList<>(options);
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

  @SuppressWarnings("unchecked")
  @Override
  public BooleanFormula getInterpolant(Collection<TFormulaInfo> pFormulasOfA)
      throws SolverException, InterruptedException {
    checkArgument(
        super.getAssertedConstraintIds().containsAll(pFormulasOfA),
        "interpolation can only be done over previously asserted formulas.");

    if (interpolationStrategy == null) {
      if (delegate instanceof InterpolatingProverEnvironment) {
        // Use native solver interpolation
        return ((InterpolatingProverEnvironment<TFormulaInfo>) delegate)
            .getInterpolant(pFormulasOfA);
      } else {
        throw new UnsupportedOperationException(
            "Solver does not natively support interpolation in JavaSMT currently.");
      }
    }

    InterpolationFormulas formulasAAndB = super.getInterpolationGroups(pFormulasOfA);
    Collection<BooleanFormula> formulasOfA = formulasAAndB.gotFormulasForA();
    Collection<BooleanFormula> formulasOfB = formulasAAndB.gotFormulasForB();

    Preconditions.checkNotNull(interpolationStrategy);

    if (interpolationStrategy.equals(ProverOptions.GENERATE_MODEL_BASED_INTERPOLANTS)) {
      return getModelBasedInterpolant(formulasOfA, formulasOfB);
    } else {
      return getQuantifierEliminationBasedInterpolant(formulasOfA, formulasOfB);
    }
  }

  @SuppressWarnings("unchecked")
  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<TFormulaInfo>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    if (interpolationStrategy == null) {
      if (delegate instanceof InterpolatingProverEnvironment) {
        // Use native solver interpolation
        return ((InterpolatingProverEnvironment<TFormulaInfo>) delegate)
            .getTreeInterpolants(partitionedFormulas, startOfSubTree);
      }
    }
    throw new UnsupportedOperationException(
        "Tree interpolants are not supported for independent interpolation currently.");
  }

  @SuppressWarnings("unchecked")
  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<TFormulaInfo>> pPartitionedFormulas)
      throws SolverException, InterruptedException {
    if (interpolationStrategy == null) {
      if (delegate instanceof InterpolatingProverEnvironment) {
        // Use native solver interpolation
        return ((InterpolatingProverEnvironment<TFormulaInfo>) delegate)
            .getSeqInterpolants(pPartitionedFormulas);
      }
    }
    throw new UnsupportedOperationException(
        "Sequential interpolants are not supported for independent interpolation currently.");
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

    BooleanFormula conjugatedA = bmgr.and(formulasOfA);
    BooleanFormula conjugatedB = bmgr.and(formulasOfB);

    List<Formula> varsOfA = getVars(conjugatedA);
    List<Formula> varsOfB = getVars(conjugatedB);

    ImmutableList<Formula> sharedVars = getSharedVars(varsOfA, varsOfB);

    checkArgument(
        !varsOfA.isEmpty(),
        "The set of variables for formulas of A is empty and cannot be quantified.");
    checkArgument(
        !varsOfB.isEmpty(),
        "The set of variables for formulas of B is empty and cannot be quantified.");
    checkArgument(
        !sharedVars.isEmpty(),
        "The set of the shared variables is empty and cannot be quantified.");

    BooleanFormula itp = getUniqueInterpolant(sharedVars);
    BooleanFormula left = qfmgr.forall(varsOfA, bmgr.implication(conjugatedA, itp));
    BooleanFormula right = qfmgr.forall(varsOfB, bmgr.implication(itp, bmgr.not(conjugatedB)));

    // check the satisfiability of the constraints and generate a model if possible
    ProverEnvironment itpProver = getDistinctProver();

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

    checkArgument(
        !varsOfA.isEmpty(),
        "The set of variables for formulas of A is empty and cannot be quantified.");
    checkArgument(
        !varsOfB.isEmpty(),
        "The set of variables for formulas of B is empty and cannot be quantified.");
    checkArgument(
        !sharedVars.isEmpty(),
        "The set of the shared variables is empty and cannot be quantified.");

    Preconditions.checkState(isUnsat());
    checkNotNull(interpolationStrategy);

    BooleanFormula interpolant = bmgr.makeFalse();
    if (interpolationStrategy.equals(ProverOptions.GENERATE_UNIFORM_BACKWARD_INTERPOLANTS)) {
      interpolant = getBackwardInterpolant(conjugatedB, varsOfB, sharedVars);
    } else if (interpolationStrategy.equals(ProverOptions.GENERATE_UNIFORM_FORWARD_INTERPOLANTS)) {
      interpolant = getForwardInterpolant(conjugatedA, varsOfA, sharedVars);
    }

    if (!satisfiesInterpolationCriteria(interpolant, conjugatedA, conjugatedB, varsOfA, varsOfB)) {
      return bmgr.makeFalse();
    }

    return interpolant;
  }

  /**
   * Computes the uniform Craig interpolant, using the quantifier-based interpolation strategy
   * utilizing quantifier-elimination in the backward direction.
   *
   * <p>Backward means, that the set of formulas B interpolates towards the set of formulas A.
   *
   * @param formulasOfB The set of formulas B, combined into one {@link BooleanFormula}.
   * @param varsOfB A list of all variables in formulas of B.
   * @param sharedVars A list of variables found in both sets of formulas A and B.
   * @return a uniform Craig interpolant, using quantifier-elimination in the backward direction.
   */
  private BooleanFormula getBackwardInterpolant(
      BooleanFormula formulasOfB, List<Formula> varsOfB, List<Formula> sharedVars) {

    BooleanFormula itpBackward = formulasOfB;

    ImmutableList<Formula> boundVars = getBoundVars(varsOfB, sharedVars);
    if (!boundVars.isEmpty()) {
      try {
        BooleanFormula itpBackwardQuantified = qfmgr.forall(boundVars, bmgr.not(formulasOfB));
        BooleanFormula itpBackwardQuantifierEliminated =
            qfmgr.eliminateQuantifiers(itpBackwardQuantified);
        // check that the quantifier has been eliminated properly
        if (itpBackwardQuantifierEliminated.equals(itpBackwardQuantified)) {
          throw new SolverException(
              "Quantifier-elimination failed. "
                  + "The resulting interpolant still contains quantifiers.");
        }
        itpBackward = itpBackwardQuantifierEliminated;
      } catch (Exception e) {
        throw new UnsupportedOperationException(
            "Solver does not support quantifier-elimination (for this logic).", e);
      }
    }

    return itpBackward;
  }

  /**
   * Computes the uniform Craig interpolant, using the quantifier-based interpolation strategy
   * utilizing quantifier-elimination in the forward direction.
   *
   * <p>Forward means, that the set of formulas A interpolates towards the set of formulas B.
   *
   * @param formulasOfA The set of formulas A, combined into one {@link BooleanFormula}.
   * @param varsOfA A list of all variables in formulas of A.
   * @param sharedVars A list of variables found in both sets of formulas A and B.
   * @return a uniform Craig interpolant, using quantifier-elimination in the forward direction.
   */
  private BooleanFormula getForwardInterpolant(
      BooleanFormula formulasOfA, List<Formula> varsOfA, List<Formula> sharedVars) {

    BooleanFormula itpForward = formulasOfA;

    ImmutableList<Formula> boundVars = getBoundVars(varsOfA, sharedVars);
    if (!boundVars.isEmpty()) {
      try {
        BooleanFormula itpForwardQuantified = qfmgr.exists(boundVars, formulasOfA);
        BooleanFormula itpForwardQuantifierEliminated =
            qfmgr.eliminateQuantifiers(itpForwardQuantified);
        // check, if the quantifier has been eliminated properly
        if (itpForwardQuantifierEliminated.equals(itpForwardQuantified)) {
          throw new SolverException(
              "Quantifier-elimination failed. "
                  + "The resulting interpolant still contains quantifiers.");
        }
        itpForward = itpForwardQuantifierEliminated;
      } catch (Exception e) {
        throw new UnsupportedOperationException(
            "Solver does not support quantifier-elimination (for this logic).", e);
      }
    }

    return itpForward;
  }

  /**
   * Identifies all variables present in a set of formulas.
   *
   * @param formulas The set of formulas combined into one {@link BooleanFormula} from which all
   *     variables will be identified.
   * @return An {@link ImmutableList} containing all variables found in the given set of formulas.
   */
  private ImmutableList<Formula> getVars(BooleanFormula formulas) {
    return ImmutableList.copyOf(mgr.extractVariablesAndUFs(formulas).values());
  }

  /**
   * Identifies the shared variables between two sets of {@link BooleanFormula}s A and B.
   *
   * @param varsOfA A list of all variables in formulas of A.
   * @param varsOfB A list of all variables in formulas of B.
   * @return An {@link ImmutableList} of all variables found in both sets of formulas A and B.
   */
  private ImmutableList<Formula> getSharedVars(List<Formula> varsOfA, List<Formula> varsOfB) {
    return varsOfA.stream().filter(varsOfB::contains).collect(ImmutableList.toImmutableList());
  }

  /**
   * Determines the variables bound to a quantifier in a quantified set of formulas used for the
   * quantifier-based interpolation strategy. These variables appear only in one set of formulas
   * (either A or B) and can be safely removed by quantifier elimination.
   *
   * @param vars A list of variables in the set of formulas to determine the bound variables.
   * @param sharedVars A list of variables found in both sets of formulas A and B.
   * @return An {@link ImmutableList} of bound variables, returns an empty list if these variables
   *     appear in both sets of formulas A and B.
   */
  private ImmutableList<Formula> getBoundVars(List<Formula> vars, List<Formula> sharedVars) {
    return vars.stream()
        .filter(var -> !sharedVars.contains(var))
        .collect(ImmutableList.toImmutableList());
  }

  /**
   * Declares and calls an uninterpreted function with a unique identifier to generate interpolants.
   *
   * @param sharedVars A list of variables found in both sets of formulas A and B.
   * @return An uninterpreted function with the {@code sharedVars} as symbols
   */
  private BooleanFormula getUniqueInterpolant(ImmutableList<Formula> sharedVars) {
    return ufmgr.declareAndCallUF(
        PREFIX + UNIQUE_ID_GENERATOR.getFreshId(), FormulaType.BooleanType, sharedVars);
  }

  /**
   * Create a new, distinct prover to interpolate on. The set of formulas for interpolation will
   * need to be translated to and from this new {@link ProverEnvironment} instance.
   *
   * @return A new {@link ProverEnvironment} configured to generate models.
   */
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
      BooleanFormula itp,
      BooleanFormula formulasOfA,
      BooleanFormula formulasOfB,
      List<Formula> varsOfA,
      List<Formula> varsOfB)
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
