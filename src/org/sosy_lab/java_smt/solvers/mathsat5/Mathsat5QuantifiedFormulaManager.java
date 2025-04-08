/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.mathsat5;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_apply_substitution;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_exists;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_forall;

import java.util.List;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class Mathsat5QuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Long, Long, Long, Long> {
  private final Long solver;

  protected Mathsat5QuantifiedFormulaManager(
      FormulaCreator<Long, Long, Long, Long> pFormulaCreator, LogManager pLogger) {
    super(pFormulaCreator, pLogger);

    solver = pFormulaCreator.getEnv();
  }

  @Override
  protected Long eliminateQuantifiers(Long input) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }

  @Override
  public Long mkQuantifier(Quantifier pQ, List<Long> pVars, Long pBody) {
    // Note: Mathsat supports this only for printing SMTLib2, not solving!
    checkArgument(!pVars.isEmpty(), "List of quantified variables can not be empty");

    long quantifiedFormula;

    long[] changeFrom = new long[pVars.size()];
    long[] changeTo = new long[pVars.size()];
    int idx = 0;
    for (Long var : pVars) {
      changeFrom[idx] = var;
      changeTo[idx] = ((Mathsat5FormulaCreator) formulaCreator).makeBoundCopy(solver, var);
      idx++;
    }

    long substBody = msat_apply_substitution(solver, pBody, 1, changeFrom, changeTo);

    if (pQ == Quantifier.EXISTS) {
      quantifiedFormula = msat_make_exists(solver, changeTo[0], substBody);
      for (int i = 1; i < changeTo.length; i++) {
        quantifiedFormula = msat_make_exists(solver, changeTo[i], substBody);
      }
    } else {
      quantifiedFormula = msat_make_forall(solver, changeTo[0], substBody);
      for (int i = 1; i < changeTo.length; i++) {
        quantifiedFormula = msat_make_forall(solver, changeTo[i], substBody);
      }
    }
    return quantifiedFormula;
  }

  @Override
  protected String dumpFormula(BooleanFormula bf) {
    return ((Mathsat5FormulaManager) getFmgr())
        .dumpFormulaImplExt(extractInfo(bf), "qFormulaNameMathsat5");
  }
}
