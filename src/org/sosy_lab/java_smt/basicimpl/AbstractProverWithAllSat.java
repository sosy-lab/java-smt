// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * This class is an utility-class to avoid repeated implementation of a the AllSAT computation.
 *
 * <p>If a solver does not support direct AllSAT computation, please inherit from this class.
 */
public abstract class AbstractProverWithAllSat<T> extends AbstractProver<T> {

  protected final ShutdownNotifier shutdownNotifier;
  private final BooleanFormulaManager bmgr;

  protected boolean closed;

  protected AbstractProverWithAllSat(
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier) {
    super(pOptions);
    bmgr = pBmgr;
    shutdownNotifier = pShutdownNotifier;
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    checkGenerateAllSat();

    push();
    while (!isUnsat()) {
      shutdownNotifier.shutdownIfNecessary();

      List<BooleanFormula> valuesOfModel = new ArrayList<>(important.size());
      try (Model model = getModelWithoutChecks()) {
        for (BooleanFormula formula : important) {
          Boolean value = model.evaluate(formula);
          if (value == null) {
            // This is a legal return value for evaluation.
            // The value doesn't matter. We ignore this assignment.
          } else if (value) {
            valuesOfModel.add(formula);
          } else {
            valuesOfModel.add(bmgr.not(formula));
          }
        }
      }

      callback.apply(valuesOfModel);
      shutdownNotifier.shutdownIfNecessary();

      BooleanFormula negatedModel = bmgr.not(bmgr.and(valuesOfModel));
      addConstraint(negatedModel);
      shutdownNotifier.shutdownIfNecessary();
    }

    pop();
    return callback.getResult();
  }

  /**
   * model computation without checks for further options.
   *
   * @throws SolverException if model can not be constructed.
   */
  protected abstract Model getModelWithoutChecks() throws SolverException;
}
