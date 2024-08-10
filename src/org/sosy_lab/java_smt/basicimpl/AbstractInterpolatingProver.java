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
import static org.sosy_lab.common.collect.Collections3.transformedImmutableSetCopy;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Term;
import java.util.Collection;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public abstract class AbstractInterpolatingProver<F> extends AbstractProverWithAllSat<F>
    implements InterpolatingProverEnvironment<F> {

  private final FormulaCreator<F, Object, Object, Object> creator;
  private final FormulaManager mgr;
  private final Set<ProverOptions> solverOptions;
  private final int seed;
  private final BooleanFormulaManager bmgr;
  private final boolean validateInterpolants;
  protected final boolean incremental;

  protected AbstractInterpolatingProver(
      Set<ProverOptions> pOptions,
      FormulaManager pMgr,
      BooleanFormulaManager pBmgr,
      FormulaCreator<F, Object, Object, Object> pCreator,
      ShutdownNotifier pShutdownNotifier,
      int randomSeed,
      boolean pValidateInterpolants) {
    super(pOptions, pBmgr, pShutdownNotifier);
    creator = pCreator;
    mgr = pMgr;
    solverOptions = pOptions;
    seed = randomSeed;
    bmgr = pBmgr;
    validateInterpolants = pValidateInterpolants;
    incremental = !enableSL;
  }

  @Override
  public BooleanFormula getInterpolant(Collection<F> pFormulasOfA)
      throws SolverException, InterruptedException {
    checkState(!closed);
    checkArgument(
        getAssertedConstraintIds().containsAll(pFormulasOfA),
        "interpolation can only be done over previously asserted formulas.");

    final Set<F> assertedFormulas =
        transformedImmutableSetCopy(getAssertedFormulas(), creator::extractInfo);
    final Set<F> formulasOfA = ImmutableSet.copyOf(pFormulasOfA);
    final Set<F> formulasOfB = Sets.difference(assertedFormulas, formulasOfA);

    F itp = getModelBasedInterpolant(formulasOfA, formulasOfB);
    return creator.encapsulateBoolean(itp);
  }

  private F getModelBasedInterpolant(Collection<F> formulasA, Collection<F> formulasB) {
    F phiPlus = (F) andImpl(formulasA);
    F phiMinus = (F) andImpl(formulasB);

    // uses a separate Solver instance to leave the original solver-context unmodified
    Solver itpSolver = new Solver();

    setSolverOptions(seed, solverOptions, itpSolver);

    F interpolant;
    try {
      itpSolver.assertFormula((Term) phiPlus); // type cast so that it works... need to be changed
      interpolant = (F) itpSolver.getInterpolant(itpSolver.mkTerm(Kind.NOT, (Term) phiMinus));
    } finally {
      itpSolver.deletePointer();
    }

    if (validateInterpolants) {
      checkModelBasedInterpolationCriteria(interpolant, phiPlus, phiMinus);
    }

    return interpolant;
  }
  
  protected BooleanFormula andImpl(Collection<F> pParams) {
    BooleanFormula result = bmgr.makeBooleanImpl(true);
    for (F formula : ImmutableSet.copyOf(pParams)) {
      if (bmgr.isFalse((BooleanFormula) formula)) {
        return (BooleanFormula) formula;
      }
      result = bmgr.and((BooleanFormula) result, (BooleanFormula) formula);
    }
    return result;
  }

  private void checkModelBasedInterpolationCriteria(F interpolant, F phiPlus, F phiMinus) {
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
    setSolverOptions(seed, solverOptions, validationSolver);
    try {
      validationSolver.push();
      validationSolver.assertFormula(validationSolver.mkTerm(Kind.IMPLIES, (Term) phiPlus,
          (Term) interpolant));
      checkState(
          validationSolver.checkSat().isSat(),
          "Invalid Craig interpolation: phi+ does not imply the interpolant.");
      validationSolver.pop();

      validationSolver.push();
      validationSolver.assertFormula(validationSolver.mkTerm(Kind.AND, (Term) interpolant,
          (Term) phiMinus));
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

  protected void setSolverOptions(int randomSeed, Set<ProverOptions> pOptions, Solver pSolver) {
    if (incremental) {
      pSolver.setOption("incremental", "true");
    }
    if (pOptions.contains(ProverOptions.GENERATE_MODELS)) {
      pSolver.setOption("produce-models", "true");
    }
    if (pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE)) {
      pSolver.setOption("produce-unsat-cores", "true");
    }
    pSolver.setOption("produce-assertions", "true");
    pSolver.setOption("dump-models", "true");
    pSolver.setOption("output-language", "smt2");
    pSolver.setOption("seed", String.valueOf(randomSeed));

    // Set Strings option to enable all String features (such as lessOrEquals)
    pSolver.setOption("strings-exp", "true");

    // Enable more complete quantifier solving (for more info see CVC5QuantifiedFormulaManager)
    pSolver.setOption("full-saturate-quant", "true");

    pSolver.setOption("produce-interpolants", "true");
  }
}
