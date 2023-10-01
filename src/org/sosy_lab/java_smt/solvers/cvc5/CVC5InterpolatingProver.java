// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableSetCopy;

import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Term;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class CVC5InterpolatingProver extends CVC5AbstractProver<Term>
    implements InterpolatingProverEnvironment<Term> {

  private final FormulaManager mgr;
  private final Set<ProverOptions> solverOptions;
  private final int seed;
  private final CVC5BooleanFormulaManager bmgr;
  private final boolean validateInterpolants;

  CVC5InterpolatingProver(
      CVC5FormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      int randomSeed,
      Set<ProverOptions> pOptions,
      FormulaManager pMgr,
      boolean pValidateInterpolants) {
    super(pFormulaCreator, pShutdownNotifier, randomSeed, pOptions, pMgr);
    mgr = pMgr;
    solverOptions = pOptions;
    seed = randomSeed;
    bmgr = (CVC5BooleanFormulaManager) mgr.getBooleanFormulaManager();
    validateInterpolants = pValidateInterpolants;
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
    checkState(!closed);
    Term t = creator.extractInfo(pConstraint);

    super.addConstraint(pConstraint);
    return t; // t is not wrapped in the Abstract Class
  }

  @Override
  public BooleanFormula getInterpolant(Collection<Term> pFormulasOfA)
      throws SolverException, InterruptedException {
    checkState(!closed);

    final Set<Term> assertedFormulas =
        transformedImmutableSetCopy(getAssertedFormulas(), creator::extractInfo);
    final Set<Term> formulasOfA = ImmutableSet.copyOf(pFormulasOfA);
    final Set<Term> formulasOfB = Sets.difference(assertedFormulas, formulasOfA);

    Term itp = getCVC5Interpolation(formulasOfA, formulasOfB);
    return creator.encapsulateBoolean(itp);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<Term>> partitions)
      throws SolverException, InterruptedException {
    Preconditions.checkArgument(
        !partitions.isEmpty(), "at least one partition should be available.");

    final int n = partitions.size();
    final List<BooleanFormula> itps = new ArrayList<>();
    Term previousItp = solver.mkTrue();
    for (int i = 1; i < n; i++) {
      Collection<Term> formulasA =
          ImmutableSet.<Term>builder().addAll(partitions.get(i - 1)).add(previousItp).build();
      Collection<Term> formulasB = FluentIterable.concat(partitions.subList(i, n)).toSet();
      Term itp = getCVC5Interpolation(formulasA, formulasB);
      itps.add(creator.encapsulateBoolean(itp));
      previousItp = itp;
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
   * @param formulasA current Set of Assertions A
   * @param formulasB Formulas to Interpolate B
   * @return Interpolation of the Interpolation Pair following the definition of
   *     Craig-Interpolation.
   */
  private Term getCVC5Interpolation(Collection<Term> formulasA, Collection<Term> formulasB) {
    Term phiPlus = bmgr.andImpl(formulasA);
    Term phiMinus = bmgr.andImpl(formulasB);

    // Uses a separate Solver instance to leave the original solver-context unmodified
    Solver itpSolver = new Solver();
    setSolverOptions(seed, solverOptions, itpSolver);

    Term interpolant;
    try {
      itpSolver.assertFormula(phiPlus);
      interpolant = itpSolver.getInterpolant(itpSolver.mkTerm(Kind.NOT, phiMinus));
    } finally {
      itpSolver.deletePointer();
    }

    if (validateInterpolants) {
      checkInterpolationCriteria(interpolant, phiPlus, phiMinus);
    }

    return interpolant;
  }

  /**
   * Checks, whether the returned interpolant indeed satisfies Craig-Interpolation and Symbol Usage.
   *
   * @param interpolant the given Interpolant for aTerm and bTerm after Craig Interpolation
   * @param phiPlus the phi+ Term in Craig Interpolation
   * @param phiMinus the phi- Term in Craig Interpolation (before negation for CVC5-Interpolation)
   */
  private void checkInterpolationCriteria(Term interpolant, Term phiPlus, Term phiMinus) {

    // checks that every Symbol of the interpolant appears either in term A or term B
    Set<String> interpolantSymbols =
        mgr.extractVariablesAndUFs(creator.encapsulateBoolean(interpolant)).keySet();
    Set<String> interpolASymbols =
        mgr.extractVariablesAndUFs(creator.encapsulateBoolean(phiPlus)).keySet();
    Set<String> interpolBSymbols =
        mgr.extractVariablesAndUFs(creator.encapsulateBoolean(phiMinus)).keySet();
    Set<String> intersection = Sets.intersection(interpolASymbols, interpolBSymbols);
    checkState(
        intersection.containsAll(interpolantSymbols),
        "Interpolant contains symbols %s that are not part of both input formulas.",
        Sets.difference(interpolantSymbols, intersection));

    // build and check both Craig interpolation formulas with the generated interpolant.
    Solver validationSolver = new Solver();
    // interpolation option is not required for validation
    super.setSolverOptions(seed, solverOptions, validationSolver);
    try {
      validationSolver.push();
      validationSolver.assertFormula(validationSolver.mkTerm(Kind.IMPLIES, phiPlus, interpolant));
      checkState(
          validationSolver.checkSat().isSat(),
          "Invalid Craig interpolation: phi+ does not imply the interpolant.");
      validationSolver.pop();

      validationSolver.push();
      validationSolver.assertFormula(validationSolver.mkTerm(Kind.AND, interpolant, phiMinus));
      checkState(
          validationSolver.checkSat().isUnsat(),
          "Invalid Craig interpolation: interpolant does not contradict phi-.");
      validationSolver.pop();

    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "Failure when validating interpolant '" + interpolant + "'.", e);

    } finally {
      validationSolver.deletePointer();
    }
  }
}
