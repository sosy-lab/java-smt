/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_FUNCTION;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_MAPPING;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YVAL_UNKNOWN;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_def_terms;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_eq;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_model;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_term_name;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_value_as_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_model_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_of_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_to_string;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;

public class Yices2Model extends CachingAbstractModel<Integer, Integer, Long> {

  private final long model;
  private final Yices2TheoremProver prover;
  private final Yices2FormulaCreator formulaCreator;
  private final boolean DEBUG_MODEL = false;
  private boolean closed = false;

  protected Yices2Model(long model, Yices2TheoremProver prover, Yices2FormulaCreator pCreator) {
    super(pCreator);
    // TODO Auto-generated constructor stub
    this.model = model;
    this.prover = prover;
    this.formulaCreator = pCreator;
    if (DEBUG_MODEL) {
      System.out.println("---MODEL_BEGIN---");
      System.out.println(yices_model_to_string(model, 100, 10, 0));
      System.out.println("---MODEL_END---");
    }
  }

  protected Yices2Model(long model, Yices2FormulaCreator creator) {
    super(creator);
    this.model = model;
    this.prover = null;
    this.formulaCreator = creator;
  }

  @Override
  public void close() {
    // TODO Auto-generated method stub
    if (!closed) {
      yices_free_model(model);
      closed = true;
    }
  }

  @Override
  protected ImmutableList<ValueAssignment> toList() {
    // TODO Auto-generated method stub
    Preconditions.checkState(!closed);
    Preconditions.checkState(!prover.isClosed(), "cannot use model after prover is closed");
    List<Integer> complex = ImmutableList.of(YVAL_FUNCTION, YVAL_MAPPING, YVAL_UNKNOWN);
    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
    int[] termsInModel = yices_def_terms(model);
    for (int i = 0; i < termsInModel.length; i++) {
      int[] yvalTag = yices_get_value(model, termsInModel[i]);
      if (!complex.contains(yvalTag[1])) {
        assignments.add(getSimpleAssignment(termsInModel[i], yvalTag));
      } else {
        throw new UnsupportedOperationException("Not yet implemented");
      }
    }

    return assignments.build();
  }

  private ValueAssignment getSimpleAssignment(int t, int[] yvalTag) {
    List<Object> argumentInterpretation = new ArrayList<>();
    int valueTerm = yices_get_value_as_term(model, t);
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(t),
        creator.encapsulateWithTypeOf(valueTerm),
        creator.encapsulateBoolean(yices_eq(t, valueTerm)),
        yices_get_term_name(t),
        formulaCreator.convertValue(valueTerm),
        argumentInterpretation);
  }
  @Override
  protected @Nullable Integer evalImpl(Integer pFormula) {
    // TODO Return term does not necessarily have same type as query term
    System.out
        .println("Query type is: " + yices_type_to_string(yices_type_of_term(pFormula), 100, 1, 0));
    Preconditions.checkState(!closed);
    // TODO reenable Preconditions.checkState(!prover.closed, "cannot use model after prover is
    // closed");
    int[] yval = yices_get_value(model, pFormula);
    System.out.println("Yval id is: " + yval[0]);
    System.out.println("Yval tag is: " + yval[1]);
    int val = yices_get_value_as_term(model, pFormula);
    if (val == -1) {
      throw new IllegalArgumentException("Term could not be evaluated!");
    }
    return val;
  }

}

