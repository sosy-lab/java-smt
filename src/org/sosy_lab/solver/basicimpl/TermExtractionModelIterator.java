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
package org.sosy_lab.solver.basicimpl;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Verify;
import com.google.common.collect.Iterables;
import com.google.common.collect.UnmodifiableIterator;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.Model.ValueAssignment;
import org.sosy_lab.solver.visitors.ExpectedFormulaVisitor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

/**
 * Helper class for writing model iterators.
 */
public abstract class TermExtractionModelIterator<E> extends UnmodifiableIterator<ValueAssignment> {
  private final Iterator<Entry<E, Object>> valuesIterator;
  private final FormulaCreator<E, ?, ?, ?> creator;

  public TermExtractionModelIterator(
      FormulaCreator<E, ?, ?, ?> creator, Iterable<E> assertedTerms) {
    checkNotNull(assertedTerms);
    this.creator = checkNotNull(creator);

    Map<E, Object> values = new HashMap<>();
    for (E t : assertedTerms) {
      for (E key : creator.extractVariablesAndUFs(t, true).values()) {
        for (Entry<E, Object> assignment : evaluate(key).entrySet()) {
          if (assignment.getValue() == null) {
            continue;
          }
          Object existingValue = values.get(assignment.getKey());
          Verify.verify(
              existingValue == null || assignment.getValue().equals(existingValue),
              "Duplicate values for model entry %s: %s and %s",
              assignment.getKey(),
              existingValue,
              assignment.getValue());
          values.put(assignment.getKey(), assignment.getValue());
        }
      }
    }
    valuesIterator = values.entrySet().iterator();
  }

  /** returns a numeric evaluation for the given key. */
  public abstract Map<E, Object> evaluate(E key);

  @Override
  public boolean hasNext() {
    return valuesIterator.hasNext();
  }

  @Override
  public ValueAssignment next() {
    Entry<E, Object> entry = valuesIterator.next();
    Formula encapsulated = creator.encapsulateWithTypeOf(entry.getKey());
    final List<Object> varInterpretation = new ArrayList<>();

    String varName =
        creator.visit(
            new ExpectedFormulaVisitor<String>() {

              @Override
              public String visitFreeVariable(Formula f, String name) {
                return name;
              }

              @Override
              public String visitFunction(
                  Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {

                // Populate argument interpretation.
                for (Formula arg : args) {
                  Object evaluation =
                      Iterables.getOnlyElement(evaluate(creator.extractInfo(arg)).values());
                  varInterpretation.add(evaluation);
                }
                return functionDeclaration.getName();
              }
            },
            encapsulated);

    return new ValueAssignment(encapsulated, varName, entry.getValue(), varInterpretation);
  }
}
