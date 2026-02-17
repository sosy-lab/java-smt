/*
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl.interpolation_techniques;

import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

public class QuantifierEliminationInterpolation extends AbstractInterpolationTechnique {

  private final ProverOptions strategy;
  private final QuantifiedFormulaManager qfmgr;

  public QuantifierEliminationInterpolation(FormulaManager pMgr, ProverOptions pStrategy) {
    super(pMgr);
    strategy = pStrategy;
    qfmgr = mgr.getQuantifiedFormulaManager();
  }

  @Override
  public BooleanFormula getInterpolant(BooleanFormula formulasOfA, BooleanFormula formulasOfB)
      throws SolverException, InterruptedException {

    List<? extends Formula> variablesInA = getAllVariables(formulasOfA);
    List<? extends Formula> variablesInB = getAllVariables(formulasOfB);
    List<Formula> sharedVariables = getCommonFormulas(variablesInA, variablesInB);

    BooleanFormula interpolant;

    if (strategy == ProverOptions.GENERATE_UNIFORM_FORWARD_INTERPOLANTS) {
      // Forward: interpolate(A(x,y),B(y,z)) = ∃x.A(x,y)
      List<Formula> exclusiveVariablesInA = removeVariablesFrom(variablesInA, sharedVariables);

      if (exclusiveVariablesInA.isEmpty()) {
        return formulasOfA;
      }

      BooleanFormula itpForwardQuantified = qfmgr.exists(exclusiveVariablesInA, formulasOfA);
      interpolant = qfmgr.eliminateQuantifiers(itpForwardQuantified);

    } else if (strategy == ProverOptions.GENERATE_UNIFORM_BACKWARD_INTERPOLANTS) {
      // Backward: interpolate(A(x,y),B(y,z))=∀z.¬B(y,z)
      List<Formula> exclusiveVariablesInB = removeVariablesFrom(variablesInB, sharedVariables);

      if (exclusiveVariablesInB.isEmpty()) {
        return bmgr.not(formulasOfB);
      }

      BooleanFormula itpBackwardQuantified =
          qfmgr.forall(exclusiveVariablesInB, bmgr.not(formulasOfB));
      interpolant = qfmgr.eliminateQuantifiers(itpBackwardQuantified);

    } else {
      throw new AssertionError("Unknown interpolation strategy for QE: " + strategy);
    }

    if (isQuantifiedFormula(interpolant)) {
      throw new SolverException(
          "Error when calculating uniform interpolant, quantifier elimination failed.");
    }

    return mgr.simplify(interpolant);
  }

  /** Checks the formula for a quantifier at an arbitrary position/depth. */
  private boolean isQuantifiedFormula(BooleanFormula maybeQuantifiedFormula) {
    final AtomicBoolean isQuantified = new AtomicBoolean(false);
    mgr.visitRecursively(
        maybeQuantifiedFormula,
        new DefaultFormulaVisitor<>() {
          @Override
          protected TraversalProcess visitDefault(Formula pF) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitQuantifier(
              BooleanFormula pF,
              Quantifier pQ,
              List<Formula> pBoundVariables,
              BooleanFormula pBody) {
            isQuantified.set(true);
            return TraversalProcess.ABORT;
          }
        });
    return isQuantified.get();
  }
}
