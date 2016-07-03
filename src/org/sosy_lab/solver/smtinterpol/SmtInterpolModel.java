/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.smtinterpol;

import com.google.common.collect.ImmutableList;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.basicimpl.AbstractModel.CachingAbstractModel;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import javax.annotation.Nullable;

class SmtInterpolModel extends CachingAbstractModel<Term, Sort, SmtInterpolEnvironment> {

  private final Model model;
  private final ImmutableList<Term> assertedTerms;
  private final SmtInterpolFormulaCreator formulaCreator;

  SmtInterpolModel(
      Model pModel,
      FormulaCreator<Term, Sort, SmtInterpolEnvironment, ?> pCreator,
      Collection<Term> assertedTerms) {
    super(pCreator);
    formulaCreator = (SmtInterpolFormulaCreator) pCreator;
    model = pModel;
    this.assertedTerms = ImmutableList.copyOf(assertedTerms);
  }

  @Nullable
  @Override
  public Object evaluateImpl(Term f) {
    Term out = model.evaluate(f);
    return getValue(out);
  }

  @Override
  protected ImmutableList<ValueAssignment> modelToList() {

    Set<ValueAssignment> assignments = new LinkedHashSet<>();

    for (Term t : assertedTerms) {
      for (Entry<String, Term> entry : creator.extractVariablesAndUFs(t, true).entrySet()) {
        assignments.add(getAssignment(entry.getKey(), (ApplicationTerm) entry.getValue()));
      }
    }

    return ImmutableList.copyOf(assignments);
  }

  private ValueAssignment getAssignment(String key, ApplicationTerm term) {
    Formula fKey = creator.encapsulateWithTypeOf(term);
    Object fValue = evaluateImpl(term);
    List<Object> argumentInterpretation = new ArrayList<>();

    for (Term param : term.getParameters()) {
      argumentInterpretation.add(evaluateImpl(param));
    }

    return new ValueAssignment(fKey, key, fValue, argumentInterpretation);
  }

  @Override
  public String toString() {
    return model.toString();
  }

  private Object getValue(Term value) {
    FormulaType<?> type = creator.getFormulaType(value);
    if (type.isBooleanType()) {
      return value.getTheory().mTrue == value;
    } else if (value instanceof ConstantTerm
        && ((ConstantTerm) value).getValue() instanceof Rational) {

      /**
       * From SmtInterpol documentation (see {@link ConstantTerm#getValue}),
       * the output is SmtInterpol's Rational unless it is a bitvector,
       * and currently we do not support bitvectors for SmtInterpol.
       */
      Rational rationalValue = (Rational) ((ConstantTerm) value).getValue();
      org.sosy_lab.common.rationals.Rational out =
          org.sosy_lab.common.rationals.Rational.of(
              rationalValue.numerator(), rationalValue.denominator());
      if (formulaCreator.getFormulaTypeOfSort(value.getSort()).isIntegerType()) {
        assert out.isIntegral();
        return out.getNum();
      } else {
        return out;
      }
    } else {

      throw new AssertionError("unexpected value: " + value);
    }
  }

  @Override
  public void close() {}
}
