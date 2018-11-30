/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSet.Builder;
import com.google.common.collect.Lists;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.FunctionValue.Index;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map.Entry;
import javax.annotation.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class SmtInterpolModel extends CachingAbstractModel<Term, Sort, SmtInterpolEnvironment> {

  private final Model model;
  private final SmtInterpolFormulaCreator formulaCreator;

  SmtInterpolModel(Model pModel, FormulaCreator<Term, Sort, SmtInterpolEnvironment, ?> pCreator) {
    super(pCreator);
    formulaCreator = (SmtInterpolFormulaCreator) pCreator;
    model = pModel;
  }

  @Nullable
  @Override
  public Object evaluateImpl(Term f) {
    return formulaCreator.convertValue(evalImpl(f));
  }

  @Override
  protected ImmutableList<ValueAssignment> toList() {

    Builder<ValueAssignment> assignments = ImmutableSet.builder();

    for (FunctionSymbol symbol : model.getDefinedFunctions()) {
      final String name = unescape(symbol.getApplicationString());
      if (symbol.getParameterSorts().length == 0) { // simple variable or array
        Term variable = creator.getEnv().term(name);
        if (symbol.getReturnSort().isArraySort()) {
          assignments.addAll(getArrayAssignment(name, variable, variable, Collections.emptyList()));
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
      String symbol, Term key, Term array, List<Object> upperIndices) {
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

        List<Object> innerIndices = Lists.newArrayList(upperIndices);
        innerIndices.add(evaluateImpl(index));

        Term select = creator.getEnv().term("select", key, index);
        if (content.getSort().isArraySort()) {
          assignments.addAll(getArrayAssignment(symbol, select, content, innerIndices));
        } else {
          assignments.add(
              new ValueAssignment(
                  creator.encapsulateWithTypeOf(select),
                  creator.encapsulateWithTypeOf(model.evaluate(content)),
                  creator.encapsulateBoolean(creator.getEnv().term("=", select, content)),
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
  private Collection<ValueAssignment> getUFAssignments(FunctionSymbol symbol) {
    final Collection<ValueAssignment> assignments = new ArrayList<>();
    final String name = unescape(symbol.getApplicationString());

    // direct interaction with internal classes and internal behaviour of SMTInterpol.
    // they made some classes 'public' especially for us,
    // because there is no nicer way of iterating over UF-assignments,
    // except building an ITE-formula in SMTInterpol and splitting it here (alternative solution).

    de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model mmodel =
        (de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model) model;

    for (Entry<Index, Integer> v : mmodel.getFunctionValue(symbol).values().entrySet()) {
      int[] indizes = v.getKey().getArray();
      Term[] arguments = new Term[indizes.length];
      for (int i = 0; i < indizes.length; i++) {
        arguments[i] = mmodel.toModelTerm(indizes[i], symbol.getParameterSorts()[i]);
      }
      assignments.add(
          getAssignment(name, (ApplicationTerm) creator.getEnv().term(name, arguments)));
    }

    return assignments;
  }

  private ValueAssignment getAssignment(String key, ApplicationTerm term) {
    Term value = model.evaluate(term);
    List<Object> argumentInterpretation = new ArrayList<>();
    for (Term param : term.getParameters()) {
      argumentInterpretation.add(evaluateImpl(param));
    }

    return new ValueAssignment(
        creator.encapsulateWithTypeOf(term),
        creator.encapsulateWithTypeOf(value),
        creator.encapsulateBoolean(creator.getEnv().term("=", term, value)),
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
