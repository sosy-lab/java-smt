// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.trace;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.SolverException;

public class TraceQuantifiedFormulaManager implements QuantifiedFormulaManager {

  private final QuantifiedFormulaManager delegate;
  private final TraceLogger logger;

  TraceQuantifiedFormulaManager(QuantifiedFormulaManager pDelegate, TraceLogger pLogger) {
    delegate = checkNotNull(pDelegate);
    logger = checkNotNull(pLogger);
  }

  private String printQuantifier(Quantifier pQuantifier) {
    return "QuantifiedFormulaManager.Quantifier." + pQuantifier.name();
  }

  @Override
  public BooleanFormula mkQuantifier(
      Quantifier q, List<? extends Formula> pVariables, BooleanFormula pBody) {
    return logger.logDef(
        "mgr.getQuantifiedFormulaManager()",
        String.format(
            "mkQuantifier(%s, List.of(%s), %s)",
            printQuantifier(q), logger.toVariables(pVariables), logger.toVariable(pBody)),
        () -> delegate.mkQuantifier(q, pVariables, pBody));
  }

  @Override
  public BooleanFormula eliminateQuantifiers(BooleanFormula pF)
      throws InterruptedException, SolverException {
    return logger.logDef(
        "mgr.getQuantifiedFormulaManager()",
        String.format("eliminateQuantifiers(%s)", logger.toVariable(pF)),
        () -> delegate.eliminateQuantifiers(pF));
  }
}
