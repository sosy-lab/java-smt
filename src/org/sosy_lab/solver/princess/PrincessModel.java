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
package org.sosy_lab.solver.princess;

import ap.SimpleAPI;
import ap.SimpleAPI.ModelValue;
import ap.SimpleAPI.PartialModel;
import ap.parser.IExpression;

import com.google.common.collect.ImmutableList;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.basicimpl.AbstractModel.CachingAbstractModel;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

import scala.Option;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import javax.annotation.Nullable;

class PrincessModel
    extends CachingAbstractModel<IExpression, PrincessTermType, PrincessEnvironment> {
  private final PartialModel model;
  private final ImmutableList<IExpression> assertedTerms;

  PrincessModel(
      PartialModel partialModel,
      FormulaCreator<IExpression, PrincessTermType, PrincessEnvironment, ?> creator,
      Collection<? extends IExpression> assertedTerms) {
    super(creator);
    this.model = partialModel;
    this.assertedTerms = ImmutableList.copyOf(assertedTerms);
  }

  @Nullable
  @Override
  public Object evaluateImpl(IExpression f) {
    Option<ModelValue> out = model.evalExpression(f);
    if (out.isEmpty()) {
      return null;
    }
    ModelValue value = out.get();
    return getValue(value);
  }

  @Override
  protected ImmutableList<ValueAssignment> modelToList() {

    Set<ValueAssignment> assignments = new LinkedHashSet<>();

    for (IExpression t : assertedTerms) {
      for (Entry<String, IExpression> entry : creator.extractVariablesAndUFs(t, true).entrySet()) {
        ValueAssignment assignment = getAssignment(entry.getKey(), entry.getValue());
        if (assignment == null) {
          // for a partial model some assignments are NULL
        } else {
          assignments.add(assignment);
        }
      }
    }

    return ImmutableList.copyOf(assignments);
  }

  private @Nullable ValueAssignment getAssignment(String key, IExpression expr) {
    Formula fKey = creator.encapsulateWithTypeOf(expr);
    Object fValue = evaluateImpl(expr);
    if (fValue == null) {
      return null; // partial model
    }

    List<Object> argumentInterpretation = new ArrayList<>();
    for (int i = 0; i < expr.length(); i++) {
      argumentInterpretation.add(evaluateImpl(expr.apply(i)));
    }
    return new ValueAssignment(fKey, key, fValue, argumentInterpretation);
  }

  @Override
  public String toString() {
    return model.toString();
  }

  private Object getValue(SimpleAPI.ModelValue value) {
    if (value instanceof SimpleAPI.BoolValue) {
      return ((SimpleAPI.BoolValue) value).v();

    } else if (value instanceof SimpleAPI.IntValue) {
      return ((SimpleAPI.IntValue) value).v().bigIntValue();

    } else {
      throw new IllegalArgumentException(
          "unhandled model value " + value + " of type " + value.getClass());
    }
  }

  @Override
  public void close() {}
}
