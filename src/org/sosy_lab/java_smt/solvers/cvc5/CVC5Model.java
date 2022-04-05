// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import io.github.cvc5.api.Kind;
import io.github.cvc5.api.Solver;
import io.github.cvc5.api.Sort;
import io.github.cvc5.api.Term;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;

public class CVC5Model extends CachingAbstractModel<Term, Sort, Solver> {

  private final ImmutableList<ValueAssignment> model;
  private final Solver solver;
  private final ImmutableList<Term> assertedExpressions;
  private final CVC5AbstractProver<?> prover;
  protected boolean closed = false;

  CVC5Model(
      CVC5AbstractProver<?> pProver,
      CVC5FormulaCreator pCreator,
      Collection<Term> pAssertedExpressions) {
    super(pCreator);
    solver = creator.getEnv();
    prover = pProver;
    assertedExpressions = ImmutableList.copyOf(pAssertedExpressions);

    // We need to generate and save this at construction time as CVC4 has no functionality to give a
    // persistent reference to the model. If the SMT engine is used somewhere else, the values we
    // get out of it might change!
    model = generateModel();
  }

  @Override
  public Term evalImpl(Term f) {
    Preconditions.checkState(!closed);
    return solver.getValue(f);
  }

  private ImmutableList<ValueAssignment> generateModel() {
    ImmutableSet.Builder<ValueAssignment> builder = ImmutableSet.builder();
    // Using creator.extractVariablesAndUFs we wouldn't get accurate information anymore as we
    // translate all bound vars back to their free counterparts in the visitor!
    for (Term expr : assertedExpressions) {
      // creator.extractVariablesAndUFs(expr, true, (name, f) -> builder.add(getAssignment(f)));
      recursiveAssignmentFinder(builder, expr);
    }
    return builder.build().asList();
  }

  @SuppressWarnings("unused")
  private void recursiveAssignmentFinder(ImmutableSet.Builder<ValueAssignment> builder, Term expr) {
    /*
     * In CVC5 consts are variables! Free variables (created with mkVar() can never have a value!) If you check
     */
    /*
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
      Term body = expr.getChildren().get(1);

      recursiveAssignmentFinder(builder, body);
    } else {
      // Only nested terms (AND, OR, ...) are left
      for (Term child : expr) {
        recursiveAssignmentFinder(builder, child);
      }
    }
    */
  }

  @SuppressWarnings("unused")
  private ValueAssignment getAssignment(Term pKeyTerm) {
    List<Object> argumentInterpretation = new ArrayList<>();
    for (Term param : pKeyTerm) {
      argumentInterpretation.add(evaluateImpl(param));
    }
    // Term name = pKeyTerm.hasOperator() ? pKeyTerm.getOperator() : pKeyTerm; // extract UF name
    String nameStr = pKeyTerm.getSymbol();
    if (nameStr.startsWith("|") && nameStr.endsWith("|")) {
      nameStr = nameStr.substring(1, nameStr.length() - 1);
    }
    Term valueTerm = solver.getValue(pKeyTerm);
    Formula keyFormula = creator.encapsulateWithTypeOf(pKeyTerm);
    Formula valueFormula = creator.encapsulateWithTypeOf(valueTerm);
    BooleanFormula equation =
        creator.encapsulateBoolean(solver.mkTerm(Kind.EQUAL, pKeyTerm, valueTerm));
    Object value = creator.convertValue(pKeyTerm, valueTerm);
    return new ValueAssignment(
        keyFormula, valueFormula, equation, nameStr, value, argumentInterpretation);
  }

  @Override
  public void close() {
    prover.unregisterModel(this);
    closed = true;
  }

  @Override
  protected ImmutableList<ValueAssignment> toList() {
    return model;
  }
}
