// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverException;

public class DebuggingQuantifiedFormulaManager extends FormulaChecks
    implements QuantifiedFormulaManager {
  private final QuantifiedFormulaManager delegate;

  public DebuggingQuantifiedFormulaManager(
      QuantifiedFormulaManager pDelegate, Set<Formula> pLocalFormulas) {
    super(pLocalFormulas);
    delegate = checkNotNull(pDelegate);
  }

  @Override
  public BooleanFormula mkQuantifier(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody) {
    assertThreadLocal();
    for (Formula t : pVariables) {
      assertFormulaInContext(t);
    }
    assertFormulaInContext(pBody);
    BooleanFormula result = delegate.mkQuantifier(q, pVariables, pBody);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula eliminateQuantifiers(BooleanFormula pF)
      throws InterruptedException, SolverException {
    assertThreadLocal();
    assertFormulaInContext(pF);
    BooleanFormula result = delegate.eliminateQuantifiers(pF);
    addFormulaToContext(result);
    return result;
  }
}
