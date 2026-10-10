/*
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl.interpolation_techniques;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UFManager;

public class ModelBasedProjectionInterpolation extends AbstractInterpolationTechnique {

  private final SolverContext solverContext;
  private final UFManager ufmgr;
  private final QuantifiedFormulaManager qfmgr;

  private static final UniqueIdGenerator termIdGenerator = new UniqueIdGenerator();

  @Override
  public BooleanFormula getInterpolant(BooleanFormula formulasOfA, BooleanFormula formulasOfB)
      throws SolverException, InterruptedException {

    List<? extends Formula> variablesInA = getAllVariables(formulasOfA);
    List<? extends Formula> variablesInB = getAllVariables(formulasOfB);
    List<Formula> sharedVars = getCommonFormulas(variablesInA, variablesInB);

    BooleanFormula itp =
        ufmgr.declareAndCallUF(
            "__itp_internal_javasmt_" + termIdGenerator.getFreshId(),
            FormulaType.BooleanType,
            sharedVars);

    BooleanFormula left;
    BooleanFormula right;

    if (variablesInA.isEmpty()) {
      left = bmgr.implication(formulasOfA, itp);
    } else {
      left = qfmgr.forall(variablesInA, bmgr.implication(formulasOfA, itp));
    }

    if (variablesInB.isEmpty()) {
      right = bmgr.implication(itp, bmgr.not(formulasOfB));
    } else {
      right = qfmgr.forall(variablesInB, bmgr.implication(itp, bmgr.not(formulasOfB)));
    }

    BooleanFormula interpolant = bmgr.makeFalse();
    try (ProverEnvironment itpProver =
        solverContext.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
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

  public ModelBasedProjectionInterpolation(SolverContext pContext) {
    super(pContext.getFormulaManager());
    solverContext = pContext;
    ufmgr = mgr.getUFManager();
    qfmgr = mgr.getQuantifiedFormulaManager();
  }
}
