// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.FunctionValue.Index;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class SmtInterpolModel extends AbstractModel<Term, Sort, Script> {

  private final Model model;
  private final Script env;
  private final ImmutableList<Term> assertedTerms;

  SmtInterpolModel(
      AbstractProver<?> pProver,
      Model pModel,
      FormulaCreator<Term, Sort, Script, ?> pCreator,
      Collection<Term> pAssertedTerms) {
    super(pProver, pCreator);
    model = pModel;
    env = pCreator.getEnv();
    assertedTerms = ImmutableList.copyOf(pAssertedTerms);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() throws SolverException, InterruptedException {

    Set<FunctionSymbol> usedSymbols = new LinkedHashSet<>();
    for (Term assertedTerm : assertedTerms) {
      for (Term symbol : creator.extractVariablesAndUFs(assertedTerm, true).values()) {
        if (symbol instanceof ApplicationTerm) {
          usedSymbols.add(((ApplicationTerm) symbol).getFunction());
        }
      }
    }

    ImmutableSet.Builder<ValueAssignment> assignments = ImmutableSet.builder();

    for (FunctionSymbol symbol : model.getDefinedFunctions()) {

      // SMTInterpol also reports evaluations for unused symbols, including those from different
      // prover stacks. Thus, we ignore unused symbols. Those symbols are still shown when
      // applying model.toString().
      if (!usedSymbols.contains(symbol)) {
        continue;
      }

      final String name = unescape(symbol.getApplicationString());
      if (symbol.getParameterSorts().length == 0) { // simple variable or array
        Term variable = env.term(name);
        if (symbol.getReturnSort().isArraySort()) {
          assignments.addAll(getArrayAssignment(name, variable, variable, ImmutableList.of()));
        } else {
          assignments.add(getAssignment(name, (ApplicationTerm) variable));
        }
      } else { // uninterpreted function
        assignments.addAll(getUFAssignments(symbol));
      }
    }

    return assignments.build().asList();
  }

  private static String unescape(String s) {
    return s.startsWith("|") ? s.substring(1, s.length() - 1) : s;
  }

  /**
   * Get all modeled assignments for the given array.
   *
   * @param symbol name of the array
   * @param key term of the whole array, such that a select operation returns the evaluation,
   * @param array term of the array, such that an evaluation returns its whole content
   * @param upperIndices indices for multi-dimensional arrays
   */
  private Collection<ValueAssignment> getArrayAssignment(
      String symbol, Term key, Term array, List<Object> upperIndices)
      throws SolverException, InterruptedException {
    assert array.getSort().isArraySort();
    Collection<ValueAssignment> assignments = new ArrayList<>();
    Term evaluation = model.evaluate(array);

    // get all assignments for the current array
    while (evaluation instanceof ApplicationTerm) {
      ApplicationTerm arrayEval = (ApplicationTerm) evaluation;
      FunctionSymbol funcDecl = arrayEval.getFunction();
      Term[] params = arrayEval.getParameters();
      if (funcDecl.isIntern() && "store".equals(funcDecl.getName())) {
        Term index = params[1];
        Term content = params[2];

        List<Object> innerIndices = new ArrayList<>(upperIndices);
        innerIndices.add(evaluateImpl(index));

        Term select = env.term("select", key, index);
        if (content.getSort().isArraySort()) {
          assignments.addAll(getArrayAssignment(symbol, select, content, innerIndices));
        } else {
          assignments.add(
              new ValueAssignment(
                  creator.encapsulateWithTypeOf(select),
                  creator.encapsulateWithTypeOf(model.evaluate(content)),
                  creator.encapsulateBoolean(env.term("=", select, content)),
                  symbol,
                  evaluateImpl(content),
                  innerIndices));
        }

        evaluation = params[0]; // unwrap recursive for more values
      } else {
        // we found the basis of the array
        break;
      }
    }

    return assignments;
  }

  /** Get all modeled assignments for the UF. */
  private Collection<ValueAssignment> getUFAssignments(FunctionSymbol symbol)
      throws SolverException, InterruptedException {
    final Collection<ValueAssignment> assignments = new ArrayList<>();
    final String name = unescape(symbol.getApplicationString());

    // direct interaction with internal classes and internal behaviour of SMTInterpol.
    // they made some classes 'public' especially for us,
    // because there is no nicer way of iterating over UF-assignments,
    // except building an ITE-formula in SMTInterpol and splitting it here (alternative solution).

    de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model mmodel =
        (de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model) model;

    for (Index key : mmodel.getFunctionValue(symbol).values().keySet()) {
      assignments.add(getAssignment(name, (ApplicationTerm) env.term(name, key.toArray())));
    }

    return assignments;
  }

  private ValueAssignment getAssignment(String key, ApplicationTerm term)
      throws SolverException, InterruptedException {
    Term value = model.evaluate(term);
    List<Object> argumentInterpretation = new ArrayList<>();
    for (Term param : term.getParameters()) {
      argumentInterpretation.add(evaluateImpl(param));
    }

    return new ValueAssignment(
        creator.encapsulateWithTypeOf(term),
        creator.encapsulateWithTypeOf(value),
        creator.encapsulateBoolean(env.term("=", term, value)),
        key,
        evaluateImpl(term),
        argumentInterpretation);
  }

  @Override
  public String toString() {
    return model.toString();
  }

  @Override
  public void close() {}

  @Override
  protected Term evalImpl(Term formula) {
    return model.evaluate(formula);
  }
}
