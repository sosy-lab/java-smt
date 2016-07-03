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

import com.google.common.collect.Iterables;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.Model.ValueAssignment;
import org.sosy_lab.solver.visitors.ExpectedFormulaVisitor;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

/**
 * Helper class to evaluate models.
 */
public abstract class ValueAssignmentExtractor<E> {

  public Set<ValueAssignment> getAssignments(
      FormulaCreator<E, ?, ?, ?> creator, Iterable<E> assertedTerms) {
    checkNotNull(assertedTerms);

    Set<ValueAssignment> assignments = new LinkedHashSet<>();
    for (E t : assertedTerms) {
      for (E key : creator.extractVariablesAndUFs(t, true).values()) {
        for (Entry<E, Object> assignment : evaluate(key).entrySet()) {
          if (assignment.getValue() == null) {
            continue;
          }

          Formula encapsulated = creator.encapsulateWithTypeOf(assignment.getKey());
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
          assignments.add(
              new ValueAssignment(encapsulated, varName, assignment.getValue(), varInterpretation));
        }
      }
    }
    return assignments;
  }

  /** returns a numeric evaluation for the given key
   * or several evaluations, if the key contains several assignments. */
  public abstract Map<E, Object> evaluate(E key);
}
