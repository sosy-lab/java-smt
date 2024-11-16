// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.SmtEngine;
import edu.stanford.CVC4.Type;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

public class CVC4Model extends AbstractModel<Expr, Type, ExprManager> {

  private final ImmutableList<ValueAssignment> model;
  private final SmtEngine smtEngine;
  private final ImmutableList<Expr> assertedExpressions;
  private final CVC4TheoremProver prover;

  CVC4Model(
      CVC4TheoremProver pProver,
      CVC4FormulaCreator pCreator,
      SmtEngine pSmtEngine,
      Collection<Expr> pAssertedExpressions)
      throws InterruptedException, SolverException {
    super(pProver, pCreator);
    smtEngine = pSmtEngine;
    prover = pProver;
    assertedExpressions = ImmutableList.copyOf(pAssertedExpressions);

    // We need to generate and save this at construction time as CVC4 has no functionality to give a
    // persistent reference to the model. If the SMT engine is used somewhere else, the values we
    // get out of it might change!
    model = generateModel();
  }

  @Override
  public Expr evalImpl(Expr f) {
    // This method looks like a violation of the constraint above: the SMT engine can be changed
    // before querying this method. However, the prover guarantees to close the model before this
    // can happen.
    Preconditions.checkState(!isClosed());
    return getValue(f);
  }

  /** we need to convert the given expression into the current context. */
  private Expr getValue(Expr f) {
    return prover.exportExpr(smtEngine.getValue(prover.importExpr(f)));
  }

  private ImmutableList<ValueAssignment> generateModel()
      throws InterruptedException, SolverException {
    ImmutableSet.Builder<ValueAssignment> builder = ImmutableSet.builder();
    // Using creator.extractVariablesAndUFs we wouldn't get accurate information anymore as we
    // translate all bound vars back to their free counterparts in the visitor!
    for (Expr expr : assertedExpressions) {
      // creator.extractVariablesAndUFs(expr, true, (name, f) -> builder.add(getAssignment(f)));
      recursiveAssignmentFinder(builder, expr);
    }
    return builder.build().asList();
  }

  // TODO this method is highly recursive and should be rewritten with a proper visitor
  private void recursiveAssignmentFinder(ImmutableSet.Builder<ValueAssignment> builder, Expr expr)
      throws InterruptedException, SolverException {
    if (expr.isConst() || expr.isNull()) {
      // We don't care about consts.
      return;
    } else if (expr.isVariable() && expr.getKind() == Kind.BOUND_VARIABLE) {
      // We don't care about bound vars (not in a UF), as they don't return a value.
      return;
    } else if (expr.isVariable() || expr.getOperator().getType().isFunction()) {
      // This includes free vars and UFs, as well as bound vars in UFs !
      builder.add(getAssignment(expr));
    } else if (expr.getKind() == Kind.FORALL || expr.getKind() == Kind.EXISTS) {
      // Body of the quantifier, with bound vars!
      Expr body = expr.getChildren().get(1);

      recursiveAssignmentFinder(builder, body);
    } else {
      // Only nested terms (AND, OR, ...) are left
      for (Expr child : expr) {
        recursiveAssignmentFinder(builder, child);
      }
    }
  }

  private ValueAssignment getAssignment(Expr pKeyTerm)
      throws InterruptedException, SolverException {
    List<Object> argumentInterpretation = new ArrayList<>();
    for (Expr param : pKeyTerm) {
      argumentInterpretation.add(evaluateImpl(param));
    }
    Expr name = pKeyTerm.hasOperator() ? pKeyTerm.getOperator() : pKeyTerm; // extract UF name
    String nameStr = name.toString();
    if (nameStr.startsWith("|") && nameStr.endsWith("|")) {
      nameStr = nameStr.substring(1, nameStr.length() - 1);
    }
    Expr valueTerm = getValue(pKeyTerm);
    Formula keyFormula = creator.encapsulateWithTypeOf(pKeyTerm);
    Formula valueFormula = creator.encapsulateWithTypeOf(valueTerm);
    BooleanFormula equation =
        creator.encapsulateBoolean(creator.getEnv().mkExpr(Kind.EQUAL, pKeyTerm, valueTerm));
    Object value = creator.convertValue(pKeyTerm, valueTerm);
    return new ValueAssignment(
        keyFormula, valueFormula, equation, nameStr, value, argumentInterpretation);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return model;
  }
}
