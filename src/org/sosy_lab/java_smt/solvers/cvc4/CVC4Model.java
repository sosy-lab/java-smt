// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.SmtEngine;
import edu.stanford.CVC4.Type;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

public class CVC4Model extends AbstractModel<Expr, Type, ExprManager> {

  private final ImmutableList<ValueAssignment> model;
  private final SmtEngine smtEngine;
  private final CVC4TheoremProver prover;

  CVC4Model(
      FormulaManager pFormulaManager,
      CVC4TheoremProver pProver,
      CVC4FormulaCreator pCreator,
      SmtEngine pSmtEngine) {
    super(pFormulaManager, pProver, pCreator);
    smtEngine = pSmtEngine;
    prover = pProver;

    // We need to generate and save this at construction time as CVC4 has no functionality to give a
    // persistent reference to the model. If the SMT engine is used somewhere else, the values we
    // get out of it might change!
    model = super.asList();
  }

  @Override
  public Expr evalImpl(Expr f) {
    // This method looks like a violation of the constraint above: the SMT engine can be changed
    // before querying this method. However, the prover guarantees to close the model before this
    // can happen.
    Preconditions.checkState(!isClosed());

    // we need to convert the given expression into the current context
    return prover.exportExpr(smtEngine.getValue(prover.importExpr(f)));
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return ImmutableList.copyOf(FluentIterable.from(model).toSet());
  }
}
