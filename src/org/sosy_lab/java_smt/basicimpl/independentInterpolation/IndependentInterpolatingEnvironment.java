/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl.independentInterpolation;

import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.Sets;
import java.util.Collection;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;

public abstract class IndependentInterpolatingEnvironment<Formula>
    implements InterpolatingProverEnvironment<Formula> {

  private final FormulaManager mgr;
  private final Set<ProverOptions> solverOptions;
  private final int seed;
  private final BooleanFormulaManager bmgr;
  private final boolean validateInterpolants;

  public IndependentInterpolatingEnvironment(
      FormulaManager pMgr,
      Set<ProverOptions> pSolverOptions,
      int pSeed,
      BooleanFormulaManager pBmgr,
      boolean pValidateInterpolants) {
    super();
    mgr = pMgr;
    solverOptions = pSolverOptions;
    seed = pSeed;
    bmgr = mgr.getBooleanFormulaManager();
    validateInterpolants = pValidateInterpolants;
  }

  protected Formula getInterpolation(Collection<Formula> formulasA, Collection<Formula> formulasB) {
    Formula phiPlus = bmgr.andImpl(formulasA);
    Formula phiMinus = bmgr.andImpl(formulasB);

    // Uses a separate Solver instance to leave the original solver-context unmodified
    Solver itpSolver = new Solver();
    setSolverOptions(seed, solverOptions, itpSolver);

    Formula interpolant;
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

  protected void checkInterpolationCriteria(
      Formula interpolant,
      Formula phiPlus,
      Formula phiMinus) {

    // Checks that every Symbol of the interpolant appears either in term A or term B
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

    // Build and check both Craig interpolation formulas with the generated interpolant.
    Solver validationSolver = new Solver();
    // Interpolation option is not required for validation
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

    } catch (Exception e) {
      throw new IllegalArgumentException(
          "Failure when validating interpolant '" + interpolant + "'.", e);

    } finally {
      validationSolver.deletePointer();
    }
  }

}
