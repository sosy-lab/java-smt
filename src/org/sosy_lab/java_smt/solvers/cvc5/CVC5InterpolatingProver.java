// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Term;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class CVC5InterpolatingProver extends CVC5AbstractProver<Term>
    implements InterpolatingProverEnvironment<Term> {

  private final FormulaManager mgr;
  private final Set<ProverOptions> solverOptions;
  private final int seed;

  CVC5InterpolatingProver(
      CVC5FormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      @SuppressWarnings("unused") int randomSeed,
      Set<ProverOptions> pOptions,
      FormulaManager pMgr) {
    super(pFormulaCreator, pShutdownNotifier, randomSeed, pOptions, pMgr);
    mgr = pMgr;
    solverOptions = pOptions;
    seed = randomSeed;
  }

  /**
   * Sets the same solver Options of the Original Solver to the separate solvertoSet, except for
   * produce-interpolants which is set here. From CVC5AbstractProver Line 66
   */
  @Override
  protected void setSolverOptions(int randomSeed, Set<ProverOptions> pOptions, Solver pSolver) {
    super.setSolverOptions(randomSeed, pOptions, pSolver);
    pSolver.setOption("produce-interpolants", "true");
  }

  @Override
  public Term addConstraint(BooleanFormula pConstraint) throws InterruptedException {
    Preconditions.checkState(!closed);
    Term t = creator.extractInfo(pConstraint);

    super.addConstraint(pConstraint);
    return t; // t is not returned in the Abstract Class
  }

  @Override
  public BooleanFormula getInterpolant(Collection<Term> pFormulasOfA)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);

    if (pFormulasOfA.isEmpty()) { // Catch trivial case
      return mgr.getBooleanFormulaManager().makeBoolean(true);
    }

    // formulasOfB := assertedFormulas - pFormulasOfA
    Set<Term> formulasOfB =
        getAssertedFormulas().stream()
            .<Term>map(n -> creator.extractInfo(n))
            .filter(n -> !pFormulasOfA.contains(n))
            .collect(ImmutableSet.toImmutableSet());

    if (formulasOfB.isEmpty()) { // Catch trivial case
      return mgr.getBooleanFormulaManager().makeBoolean(false);
    }

    // fit the Input to work with getCVC5Interpolation

    ImmutableList<Collection<Term>> formAAsList = ImmutableList.of(pFormulasOfA);
    ImmutableList<Collection<Term>> formBAsList = ImmutableList.of(formulasOfB);

    Term itp = getCVC5Interpolation(formAAsList, formBAsList);

    return creator.encapsulateBoolean(itp);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(
      List<? extends Collection<Term>> partitionedFormulas)
      throws SolverException, InterruptedException {
    Preconditions.checkArgument(
        !partitionedFormulas.isEmpty(), "at least one partition should be available.");

    final List<BooleanFormula> itps = new ArrayList<>();

    if (partitionedFormulas.size() == 1) {
      return itps;
    }
    itps.add(
        getInterpolant(ImmutableList.copyOf(Iterables.concat(partitionedFormulas.subList(0, 1)))));
    Integer n = partitionedFormulas.size();
    for (int i = 2; i < n; i++) {
      Term preInterpol = creator.extractInfo(itps.get(i - 2));
      Term currFormulaInterpol =
          getCVC5Interpolation(
              ImmutableList.of(ImmutableSet.of(preInterpol), partitionedFormulas.get(i - 1)),
              ImmutableList.of(
                  ImmutableList.copyOf(Iterables.concat(partitionedFormulas.subList(i, n)))));
      itps.add(creator.encapsulateBoolean(currFormulaInterpol));
    }

    return itps;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<Term>> partitionedFormulas, int[] startOfSubTree) {
    throw new UnsupportedOperationException(
        "directly receiving tree interpolants is not supported."
            + "Use another solver or another strategy for interpolants.");
  }

  /**
   * Interpolates a Tuple of Interpolants according to Craig-Interpolation using CVC5-Interpolation.
   *
   * <p>CVC5's getInterpolant: There is a Model, such that the Interpolant I, with A -> I = True
   * (1CVC5) and I -> B = True (2CVC5).
   *
   * <p>Craig Interpolation: There is a Model, such that the Interpolant psi, with phi- -> psi =
   * True (1Craig), not(psi /\ phi+) = True (2Craig).
   *
   * <p>With A/phi- current set of assertions and B/phi+ Formulas to interpolate.
   *
   * <p>CVC5 -> Craig Interpolation:
   *
   * <p>(1CVC5) <=> (1Craig) due to subst of A with phi- and reflexivity.
   *
   * <p>(2CVC5) <=> I -> B = True <=> (not I) \/ B = True <=> not (I /\ (not B)) = True <=> (2Craig)
   * due to subst of (not B) with phi+ and reflexivity.
   *
   * <p>Hence, CVC5's Interpolation produces an equivalent Interpolation to Craig Interpolation, if
   * B is negated during CVC5 Interpolation.
   *
   * @param pFormAAsList current Set of Assertions A
   * @param pFormBAsList Formulas to Interpolate B
   * @return Interpolation of the Interpolation Pair following the definition of
   *     Craig-Interpolation.
   */
  private Term getCVC5Interpolation(
      ImmutableList<Collection<Term>> pFormAAsList, ImmutableList<Collection<Term>> pFormBAsList) {

    // Uses a separate Solver instance to leave the original solver-context unmodified
    Solver interpolationSolver = new Solver();

    setSolverOptions(seed, solverOptions, interpolationSolver);

    Term interpolA = buildConjunctionOfFormulasOverList(pFormAAsList, interpolationSolver);

    Term interpolB = buildConjunctionOfFormulasOverList(pFormBAsList, interpolationSolver);

    interpolationSolver.assertFormula(interpolA);

    Term interpolant =
        interpolationSolver.getInterpolant(interpolationSolver.mkTerm(Kind.NOT, interpolB));

    checkCVC5Interpolation(interpolationSolver, interpolant, interpolA, interpolB);

    interpolationSolver.deletePointer();

    return interpolant;
  }

  /**
   * Turns a List of Collections of Formulas to a Single Conjunction of the Formulas e.g.:
   * [[A,B],[C]] -> A/\B/\C.
   *
   * @param setOfFormulasToConcat List of Collections of formulas
   * @param usingSolver the CVC5 Solver Instance to use
   * @return concatenated Formulas with AND as CVC5 Term
   */
  private Term buildConjunctionOfFormulasOverList(
      ImmutableList<Collection<Term>> setOfFormulasToConcat, Solver usingSolver) {
    Term concatTerm =
        buildConjunctionOfFormulas(
            FluentIterable.concat(setOfFormulasToConcat).toSet(), usingSolver);

    return concatTerm;
  }

  /**
   * Turns a collection of Formulas to a Single Conjunction of the Formulas e.g.: [A,B,C] ->
   * A/\B/\C.
   *
   * @param formulas collection of formulas
   * @param usingSolver the CVC5 Solver Instance to use
   * @return concatenated Formulas with AND as CVC5 Term
   */
  private Term buildConjunctionOfFormulas(Collection<Term> formulas, Solver usingSolver) {
    Preconditions.checkState(!closed);
    Preconditions.checkArgument(!formulas.isEmpty());

    switch (formulas.size()) {
      case 0:
        return usingSolver.mkBoolean(true);
      case 1:
        return Iterables.getOnlyElement(formulas);
      default:
        return usingSolver.mkTerm(Kind.AND, formulas.toArray(new Term[0]));
    }
  }

  /**
   * Checks, whether the returned interpolant indeed satisfies Craig-Interpolation and Symbol Usage.
   *
   * @param solverP the Solver to use to check for SAT and UNSAT
   * @param interpolant the given Interpolant for aTerm and bTerm after Craig Interpolation
   * @param aTerm the phi+ Term in Craig Interpolation
   * @param bTerm the phi- Term in Craig Interpolation (before negation for CVC5-Interpolation)
   */
  private void checkCVC5Interpolation(Solver solverP, Term interpolant, Term aTerm, Term bTerm) {
    ImmutableMap<String, Formula> interpolantSymbols =
        mgr.extractVariablesAndUFs(creator.encapsulateBoolean(interpolant));
    ImmutableMap<String, Formula> interpolASymbols =
        mgr.extractVariablesAndUFs(creator.encapsulateBoolean(aTerm));
    ImmutableMap<String, Formula> interpolBSymbols =
        mgr.extractVariablesAndUFs(creator.encapsulateBoolean(bTerm));

    // checks that every Symbol of the interpolant appears either in term A or term B
    boolean interpolSymbolMatch = true;
    for (String key : interpolantSymbols.keySet()) {
      if (!interpolASymbols.containsKey(key) && !interpolBSymbols.containsKey(key)) {
        interpolSymbolMatch = false;
      }
    }

    Preconditions.checkArgument(interpolSymbolMatch, "Interpolant contains Symbols not in A or B.");

    // we are reusing the InterpolationSolver instance, so we must reset it
    solverP.resetAssertions();

    // build both Craig Interpolation Formulas with generated interpolant and given Formulas
    Term craig1 = solverP.mkTerm(Kind.IMPLIES, aTerm, interpolant);
    Term craig2 = solverP.mkTerm(Kind.AND, interpolant, bTerm);

    solverP.assertFormula(craig1);
    // assert solverP.checkSat().isSat() : "Interpolant does not follow Craig Interpolation";

    solverP.resetAssertions();

    solverP.assertFormula(craig2);
    assert solverP.checkSat().isUnsat() : "Interpolant does not follow Craig Interpolation";
  }
}
