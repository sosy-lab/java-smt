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
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
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
    return List.of();
  }

  private BooleanFormula getModelBasedInterpolant(
      Collection<BooleanFormula> pFormulasOfA, Collection<BooleanFormula> pFormulasOfB) {

    BooleanFormula formulasOfA = bmgr.and(pFormulasOfA);
    BooleanFormula formulasOfB = bmgr.and(pFormulasOfB);

    // free arithmetic variables A and B
    List<Formula> arithVarsOfA = new ArrayList<>(mgr.extractVariablesAndUFs(formulasOfA).values());
    List<Formula> arithVarsOfB = new ArrayList<>(mgr.extractVariablesAndUFs(formulasOfB).values());

    // shared variables between A and B
    ImmutableList<Formula> sharedVariables = arithVarsOfA.stream()
        .filter(arithVarsOfB::contains)
        .collect(ImmutableList.toImmutableList());

    BooleanFormula itp = ufmgr.declareAndCallUF(
        "Func_model-based_craig-itp", FormulaType.BooleanType, sharedVariables);

    BooleanFormula left = qfmgr.forall(arithVarsOfA, bmgr.and(bmgr.implication(formulasOfA, itp)));
    BooleanFormula right = qfmgr.forall(arithVarsOfB, bmgr.and(bmgr.implication(itp,
        bmgr.not(formulasOfB))));

    return null;
  }
}
