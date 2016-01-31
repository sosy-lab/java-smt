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

import com.google.common.base.Function;
import com.google.common.base.Optional;

import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.basicimpl.AbstractModel;
import org.sosy_lab.solver.basicimpl.FormulaCreator;
import org.sosy_lab.solver.basicimpl.TermExtractionModelIterator;

import java.util.Collection;
import java.util.Iterator;

class SmtInterpolModel extends AbstractModel<Term, Sort, SmtInterpolEnvironment> {

  private final Model model;
  private final Collection<Term> assertedTerms;

  SmtInterpolModel(
      Model pModel,
      FormulaCreator<Term, Sort, SmtInterpolEnvironment> pCreator,
      Collection<Term> assertedTerms) {
    super(pCreator);
    model = pModel;
    this.assertedTerms = assertedTerms;
  }

  @Override
  public Optional<Object> evaluate(Term f) {
    Term out = model.evaluate(f);
    return Optional.of(getValue(out));
  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    return new TermExtractionModelIterator<>(
        creator,
        new Function<Term, Optional<Object>>() {
          @Override
          public Optional<Object> apply(Term input) {
            return evaluate(input);
          }
        },
        assertedTerms);
  }

  @Override
  public String toString() {
    return model.toString();
  }

  private Object getValue(Term value) {
    FormulaType<?> type = creator.getFormulaType(value);
    if (type.isBooleanType()) {
      return SmtInterpolUtil.isTrue(value);
    } else if (SmtInterpolUtil.isNumber(value)) {
      return SmtInterpolUtil.toNumber(value);
    } else {

      // Return string serialization for unknown values.
      return value.toString();
    }
  }
}
