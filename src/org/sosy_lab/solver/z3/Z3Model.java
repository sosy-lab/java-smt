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
package org.sosy_lab.solver.z3;

import static org.sosy_lab.solver.z3.Z3NativeApi.ast_to_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_eval;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_to_string;

import com.google.common.base.Function;
import com.google.common.base.Verify;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.basicimpl.AbstractModel;
import org.sosy_lab.solver.basicimpl.TermExtractionModelIterator;
import org.sosy_lab.solver.z3.Z3NativeApi.PointerToLong;

import java.util.Iterator;
import java.util.List;

import javax.annotation.Nullable;

class Z3Model extends AbstractModel<Long, Long, Long> {

  private final long model;
  private final long z3context;
  private final Z3FormulaCreator creator;
  private final ImmutableList<BooleanFormula> trackedConstraints;

  Z3Model(
      long z3context,
      long z3model,
      Z3FormulaCreator pCreator,
      List<BooleanFormula> pTrackedConstraints) {
    super(pCreator);
    model_inc_ref(z3context, z3model);
    model = z3model;
    this.z3context = z3context;
    creator = pCreator;
    trackedConstraints = ImmutableList.copyOf(pTrackedConstraints);
  }

  @Nullable
  @Override
  public Object evaluateImpl(Long f) {
    PointerToLong out = new PointerToLong();
    boolean status = model_eval(z3context, model, f, true, out);
    Verify.verify(status, "Error during model evaluation");
    if (out.value == 0) {
      return null;
    }
    return creator.convertValue(out.value);
  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    return new TermExtractionModelIterator<>(
        creator,
        new Function<Long, Object>() {
          @Override
          public Object apply(Long input) {
            return evaluateImpl(input);
          }
        },
        Iterables.transform(trackedConstraints, creator.extractInfo));
  }

  @Override
  public String toString() {
    return model_to_string(z3context, model);
  }

  /** Delays the conversion to string. */
  private static class LazyString {

    final long value;
    final long z3context;

    LazyString(long v, long pZ3context) {
      value = v;
      z3context = pZ3context;
    }

    @Override
    public String toString() {
      return ast_to_string(z3context, value); // this could be an expensive operation!
    }
  }
}
