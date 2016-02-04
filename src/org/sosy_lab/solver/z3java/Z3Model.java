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
package org.sosy_lab.solver.z3java;

import com.google.common.base.Function;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.basicimpl.AbstractModel;
import org.sosy_lab.solver.basicimpl.TermExtractionModelIterator;

import java.util.Iterator;
import java.util.List;

import javax.annotation.Nullable;

class Z3Model extends AbstractModel<Expr, Sort, Context> {

  private final com.microsoft.z3.Model model;
  private final ImmutableList<BooleanFormula> trackedConstraints;

  @SuppressWarnings("hiding")
  private final Z3FormulaCreator creator;

  Z3Model(com.microsoft.z3.Model pModel, Z3FormulaCreator pCreator,
      List<BooleanFormula> pTrackedConstraints) {
    super(pCreator);
    model = pModel;
    creator = pCreator;
    trackedConstraints = ImmutableList.copyOf(pTrackedConstraints);
  }

  @Nullable
  @Override
  public Object evaluateImpl(Expr f) {
    return creator.convertValue(model.eval(f, true));
  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    return new TermExtractionModelIterator<>(
        creator,
        new Function<Expr, Object>() {
          @Override
          public Object apply(Expr input) {
            return evaluateImpl(input);
          }
        },
        Iterables.transform(trackedConstraints, creator.extractInfo));
  }

  @Override
  public String toString() {
    return model.toString();
  }
}
