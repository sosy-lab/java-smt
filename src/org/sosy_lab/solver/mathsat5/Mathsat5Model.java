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
package org.sosy_lab.solver.mathsat5;

import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_destroy_model;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_destroy_model_iterator;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_model;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_model_create_iterator;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_model_eval;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_model_iterator_has_next;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_model_iterator_next;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_arity;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_get_arg;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableList.Builder;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.basicimpl.AbstractModel;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import javax.annotation.Nullable;

class Mathsat5Model extends AbstractModel<Long, Long, Long> {

  private final long model;
  private final Mathsat5FormulaCreator formulaCreator;
  private @Nullable ImmutableList<ValueAssignment> modelAssignments = null;

  private Mathsat5Model(long model, Mathsat5FormulaCreator creator) {
    super(creator);
    this.model = model;
    formulaCreator = creator;
  }

  static Mathsat5Model create(Mathsat5FormulaCreator creator, long msatEnv) {
    return new Mathsat5Model(msat_get_model(msatEnv), creator);
  }

  @Override
  public Object evaluateImpl(Long f) {
    long term = msat_model_eval(model, f);
    return formulaCreator.convertValue(f, term);
  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    if (modelAssignments == null) {
      modelAssignments = generateAssignments();
    }
    return modelAssignments.iterator();
  }

  ImmutableList<ValueAssignment> generateAssignments() {
    Builder<ValueAssignment> assignments = ImmutableList.builder();

    long modelIterator = msat_model_create_iterator(model);
    while (msat_model_iterator_has_next(modelIterator)) {
      long[] key = new long[1];
      long[] value = new long[1];
      if (msat_model_iterator_next(modelIterator, key, value)) {
        throw new NoSuchElementException();
      }
      Formula fKey = creator.encapsulateWithTypeOf(key[0]);
      Object fValue = formulaCreator.convertValue(key[0], value[0]);
      List<Object> argumentInterpretation = new ArrayList<>();

      for (int i = 0; i < msat_term_arity(key[0]); i++) {
        long arg = msat_term_get_arg(key[0], i);
        argumentInterpretation.add(evaluateImpl(arg));
      }

      assignments.add(
          new ValueAssignment(
              fKey, formulaCreator.getName(key[0]), fValue, argumentInterpretation));
    }
    msat_destroy_model_iterator(modelIterator);
    return assignments.build();
  }

  @Override
  public void close() {
    msat_destroy_model(model);
  }
}
