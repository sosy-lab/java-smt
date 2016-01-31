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
import static org.sosy_lab.solver.z3.Z3NativeApi.dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_decl;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_arity;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_decl_name;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_symbol_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_symbol_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_app;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_eval;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_const_decl;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_const_interp;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_num_consts;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_to_string;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_STRING_SYMBOL;

import com.google.common.base.Optional;
import com.google.common.base.Preconditions;
import com.google.common.base.Verify;
import com.google.common.collect.UnmodifiableIterator;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.basicimpl.AbstractModel;
import org.sosy_lab.solver.basicimpl.Model;
import org.sosy_lab.solver.z3.Z3NativeApi.PointerToLong;

import java.util.Iterator;

class Z3Model extends AbstractModel<Long, Long, Long> {

  private final long model;
  private final long z3context;
  private final Z3FormulaCreator creator;

  Z3Model(long z3context, long z3model, Z3FormulaCreator pCreator) {
    super(pCreator);
    model_inc_ref(z3context, z3model);
    model = z3model;
    this.z3context = z3context;
    creator = pCreator;
  }

  public static Model parseZ3Model(long z3context, long z3model, Z3FormulaCreator pCreator) {
    return new Z3Model(z3context, z3model, pCreator);
  }

  @Override
  public Optional<Object> evaluate(Long f) {
    PointerToLong out = new PointerToLong();
    boolean status = model_eval(z3context, model, f, true, out);
    Verify.verify(status, "Error during model evaluation");
    if (out.value == 0) {
      return Optional.absent();
    }
    return Optional.of(creator.convertValue(out.value));
  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    return new Z3ModelIterator();
  }

  private class Z3ModelIterator extends UnmodifiableIterator<ValueAssignment> {
    final int numConsts;
    int cursor = 0;

    Z3ModelIterator() {
      // TODO: iterating through function applications.
      numConsts = model_get_num_consts(z3context, model);
    }

    @Override
    public boolean hasNext() {
      return cursor != numConsts;
    }

    @Override
    public ValueAssignment next() {
      long keyDecl = model_get_const_decl(z3context, model, cursor++);
      inc_ref(z3context, keyDecl);

      Preconditions.checkArgument(
          get_arity(z3context, keyDecl) == 0, "Declaration is not a constant");

      long var = mk_app(z3context, keyDecl);
      Formula key = creator.encapsulateWithTypeOf(var);

      long value = model_get_const_interp(z3context, model, keyDecl);
      inc_ref(z3context, value);

      long decl = get_app_decl(z3context, var);
      long symbol = get_decl_name(z3context, decl);

      Preconditions.checkArgument(
          get_symbol_kind(z3context, symbol) == Z3_STRING_SYMBOL,
          "Given symbol of expression is no stringSymbol! (%s)",
          new LazyString(var, z3context));

      String lName = get_symbol_string(z3context, symbol);
      Object lValue = creator.convertValue(value);

      // cleanup outdated data
      dec_ref(z3context, keyDecl);
      dec_ref(z3context, value);

      return new ValueAssignment(key, lValue);
    }
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
