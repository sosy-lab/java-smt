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
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableList;
import java.util.Collection;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UFManager;

public abstract class AbstractInterpolatingProver<TFormulaInfo extends Formula, TType>
        extends AbstractProverWithAllSat<TFormulaInfo>
        implements InterpolatingProverEnvironment<TFormulaInfo> {

  private final FormulaManager mgr;
  private final BooleanFormulaManager bmgr;
  private final UFManager ufmgr;
  private final QuantifiedFormulaManager qfmgr;

  private static final UniqueIdGenerator UNIQUE_ID_GENERATOR = new UniqueIdGenerator();
  private static final String PREFIX = "__internal_model_itp_generation_";

  protected AbstractInterpolatingProver(
          Set<ProverOptions> pOptions,
          FormulaManager pMgr,
          BooleanFormulaManager pBmgr,
          UFManager pUfmgr,
          QuantifiedFormulaManager pQfmgr,
          ShutdownNotifier pShutdownNotifier) {
    super(pOptions, pMgr, pBmgr, pQfmgr, pShutdownNotifier);
    mgr = pMgr;
    bmgr = pBmgr;
    ufmgr = pUfmgr;
    qfmgr = pQfmgr;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<TFormulaInfo> pFormulasOfA)
          throws SolverException, InterruptedException {
    checkState(!closed);
    checkArgument(getAssertedConstraintIds().containsAll(pFormulasOfA),
        "interpolation can only be done over previously asserted formulas.");

    final ImmutableCollection<BooleanFormula> assertedFormulas =
        ImmutableList.copyOf(getAssertedFormulas());

    final Collection<BooleanFormula> formulasOfA =
        (Collection<BooleanFormula>) ImmutableList.copyOf(pFormulasOfA);
    final Collection<BooleanFormula> formulasOfB =
        assertedFormulas.stream()
            .filter(formula -> !formulasOfA.contains(formula))
            .collect(ImmutableList.toImmutableList());

    return getModelBasedInterpolant(formulasOfA, formulasOfB);
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<TFormulaInfo>> partitionedFormulas,
      int[] startOfSubTree) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException(
        "directly receiving tree interpolants is not supported. "
            + "Use another strategy for interpolants.");
  }

  private BooleanFormula getModelBasedInterpolant(
      Collection<BooleanFormula> pFormulasOfA, Collection<BooleanFormula> pFormulasOfB)
      throws InterruptedException, SolverException {

    final ImmutableList<BooleanFormula> originalStack = ImmutableList.copyOf(getAssertedFormulas());

    clearStack();

    BooleanFormula interpolant = computeModelBasedInterpolant(pFormulasOfA, pFormulasOfB);

    restoreStack(originalStack);

    return interpolant;
  }

  /**
   * Computes Craig interpolants for a pair of formulas using a model-based approach.
   *
   * <p>The model-based approach takes two groups of Boolean formulas, A and B, as input and
   * returns an interpolant Itp. The interpolant Itp satisfies the definition of Craig
   * interpolation, meaning:
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

    BooleanFormula formulasOfA = bmgr.and(pFormulasOfA);
    BooleanFormula formulasOfB = bmgr.and(pFormulasOfB);

    List<Formula> varsOfA = getVars(formulasOfA);
    List<Formula> varsOfB = getVars(formulasOfB);

    ImmutableList<Formula> sharedVars = getSharedVars(varsOfA, varsOfB);

    BooleanFormula itp = getUniqueInterpolant(sharedVars);
    BooleanFormula left = qfmgr.forall(varsOfA, bmgr.implication(formulasOfA, itp));
    BooleanFormula right = qfmgr.forall(varsOfB, bmgr.implication(itp, bmgr.not(formulasOfB)));

    push(bmgr.and(left, right)); // solve left and right

    if (isUnsat()) {
      return bmgr.makeFalse(); // return false as the interpolant
    }

    return Objects.requireNonNull(getModel().eval(itp));
  }

  /**
   * Extracts all free variables and uninterpreted functions from the input Boolean formula.
   *
   * @param formulas The input Boolean formula from which to extract all free arithmetic variables.
   * @return A list of all free variables and uninterpreted functions of the input formula.
   */
  private ImmutableList<Formula> getVars(BooleanFormula formulas) {
    return ImmutableList.copyOf(mgr.extractVariablesAndUFs(formulas).values());
  }

  /**
   * Identifies the shared variables between two formulas A and B.
   *
   * @param varsOfA A list of free variables extracted from formula A.
   * @param varsOfB A list of free variables extracted from formula B.
   * @return An immutable list of variables found in both formulas A and B.
   */
  private ImmutableList<Formula> getSharedVars(List<Formula> varsOfA, List<Formula> varsOfB) {
    return varsOfA.stream()
        .filter(varsOfB::contains)
        .collect(ImmutableList.toImmutableList());
  }

  private BooleanFormula getUniqueInterpolant(ImmutableList<Formula> sharedVars) {
    return ufmgr.declareAndCallUF(
        PREFIX + UNIQUE_ID_GENERATOR.getFreshId(),
        FormulaType.BooleanType,
        sharedVars);
  }

  private void clearStack() {
    for (int i = 0; i < size(); i++) {
      pop();
    }
  }

  private void restoreStack(List<BooleanFormula> assertedFormulas) throws InterruptedException {
    for (BooleanFormula formula : assertedFormulas) {
      push(formula);
    }
  }
}
