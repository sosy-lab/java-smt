// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.io.IOException;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class DebuggingQuantifiedFormulaManager implements QuantifiedFormulaManager {
  private final QuantifiedFormulaManager delegate;
  private final DebuggingAssertions debugging;
  private ProverOptions[] option;

  public DebuggingQuantifiedFormulaManager(
      QuantifiedFormulaManager pDelegate, DebuggingAssertions pDebugging) {
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public BooleanFormula mkQuantifier(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody) {
    debugging.assertThreadLocal();
    for (Formula t : pVariables) {
      debugging.assertFormulaInContext(t);
    }
    debugging.assertFormulaInContext(pBody);
    BooleanFormula result = delegate.mkQuantifier(q, pVariables, pBody);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula eliminateQuantifiers(BooleanFormula pF)
      throws InterruptedException, SolverException, IOException {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(pF);
    BooleanFormula result = delegate.eliminateQuantifiers(pF);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public ProverOptions[] getOptions() {
    return option;
  }

  @Override
  public void setOptions(ProverOptions... opt) {
    option = opt;
  }
}
