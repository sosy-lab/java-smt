// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Preconditions;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.SmtEngine;
import edu.stanford.CVC4.Type;
import org.sosy_lab.java_smt.basicimpl.AbstractEvaluator;

public class CVC4Evaluator extends AbstractEvaluator<Expr, Type, ExprManager> {

  private final SmtEngine smtEngine;
  private final CVC4TheoremProver prover;

  CVC4Evaluator(
      CVC4TheoremProver pProver,
      CVC4FormulaManager pFormulaManager,
      SmtEngine pSmtEngine) {
    super(pProver, pFormulaManager);
    smtEngine = pSmtEngine;
    prover = pProver;
  }

  @Override
  public Expr evalImpl(Expr f) {
    Preconditions.checkState(!isClosed());
    return getValue(f);
  }

  /**
   * we need to convert the given expression into the current context.
   */
  private Expr getValue(Expr f) {
    return prover.exportExpr(smtEngine.getValue(prover.importExpr(f)));
  }
}
