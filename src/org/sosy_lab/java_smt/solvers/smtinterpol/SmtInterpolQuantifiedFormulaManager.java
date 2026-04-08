/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableMap;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class SmtInterpolQuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Term, Sort, Script, FunctionSymbol> {
  protected SmtInterpolQuantifiedFormulaManager(
      FormulaCreator<Term, Sort, Script, FunctionSymbol> pCreator) {
    super(pCreator);
  }

  @Override
  protected Term eliminateQuantifiers(Term pExtractInfo)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }

  /** Replace free variables with bound variables. */
  private Term substFreeVariables(Map<Term, TermVariable> pSubst, Term pTerm) {
    if (pTerm instanceof ApplicationTerm application) {
      var args = application.getParameters();
      if (args.length == 0) {
        return pSubst.containsKey(pTerm) ? pSubst.get(pTerm) : pTerm;
      } else {
        return formulaCreator.callFunctionImpl(
            application.getFunction(),
            FluentIterable.from(args).transform(p -> substFreeVariables(pSubst, p)).toList());
      }
    } else if (pTerm instanceof ConstantTerm constant) {
      return constant;
    } else if (pTerm instanceof TermVariable variable) {
      return variable;
    } else if (pTerm instanceof AnnotatedTerm annotated) {
      throw new IllegalArgumentException("Unexpected 'annotated' term: %s".formatted(annotated));
    } else if (pTerm instanceof LambdaTerm lambda) {
      throw new IllegalArgumentException("Unexpected 'lambda' term: %s".formatted(lambda));
    } else if (pTerm instanceof LetTerm let) {
      throw new IllegalArgumentException("Unexpected 'let' term: %s".formatted(let));
    } else if (pTerm instanceof MatchTerm match) {
      throw new IllegalArgumentException("Unexpected 'match' term: %s".formatted(match));
    } else if (pTerm instanceof QuantifiedFormula quantified) {
      formulaCreator
          .getEnv()
          .quantifier(
              quantified.getQuantifier(),
              quantified.getVariables(),
              substFreeVariables(pSubst, quantified.getSubformula()));
    } else {
      throw new AssertionError();
    }
    return pTerm;
  }

  @Override
  public Term mkQuantifier(Quantifier q, List<Term> vars, Term body) {
    var quantifier =
        switch (q) {
          case FORALL -> QuantifiedFormula.FORALL;
          case EXISTS -> QuantifiedFormula.EXISTS;
        };

    ImmutableMap.Builder<Term, TermVariable> builder = ImmutableMap.builder();
    for (Term var : vars) {
      builder.put(
          var,
          formulaCreator
              .getEnv()
              .variable(((ApplicationTerm) var).getFunction().getName(), var.getSort()));
    }

    var newVars = builder.build();
    var newBody = substFreeVariables(newVars, body);

    return formulaCreator
        .getEnv()
        .quantifier(quantifier, newVars.values().toArray(new TermVariable[0]), newBody);
  }
}
