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

import static org.sosy_lab.solver.z3.Z3NativeApi.dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_entry_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_entry_get_arg;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_entry_get_num_args;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_entry_get_value;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_entry_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_interp_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_interp_get_entry;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_interp_get_num_entries;
import static org.sosy_lab.solver.z3.Z3NativeApi.func_interp_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_arity;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_decl_name;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_symbol_int;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_symbol_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_symbol_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_app;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_eval;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_const_decl;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_const_interp;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_func_decl;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_func_interp;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_num_consts;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_get_num_funcs;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_inc_ref;

import com.google.common.base.Preconditions;
import com.google.common.base.Verify;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableList.Builder;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.basicimpl.AbstractModel;
import org.sosy_lab.solver.z3.Z3NativeApi.PointerToLong;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import javax.annotation.Nullable;

class Z3Model extends AbstractModel<Long, Long, Long> {

  private final long model;
  private final long z3context;

  @SuppressWarnings("hiding")
  private final Z3FormulaCreator creator;

  private @Nullable ImmutableList<ValueAssignment> assignments = null;

  private Z3Model(long z3context, long z3model, Z3FormulaCreator pCreator) {
    super(pCreator);
    model_inc_ref(z3context, z3model);
    model = z3model;
    this.z3context = z3context;
    creator = pCreator;
  }

  static Z3Model create(long z3context, long z3model, Z3FormulaCreator pCreator) {
    Z3Model model = new Z3Model(z3context, z3model, pCreator);
    pCreator.storeModelPhantomReference(model, z3model);
    pCreator.cleanupModelReferences();
    return model;
  }

  @Nullable
  @Override
  public Object evaluateImpl(Long f) {
    PointerToLong out = new PointerToLong();
    boolean status = model_eval(z3context, model, f, false, out);
    Verify.verify(status, "Error during model evaluation");
    long outValue = out.value;

    if (creator.isConstant(outValue)) {
      return creator.convertValue(outValue);
    }
    return null;
  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    if (assignments == null) {

      // Cache model values.
      assignments = modelToList();
    }
    return assignments.iterator();
  }

  private ImmutableList<ValueAssignment> modelToList() {
    Builder<ValueAssignment> out = ImmutableList.builder();

    // Iterate through constants.
    for (int i = 0; i < model_get_num_consts(z3context, model); i++) {
      long keyDecl = model_get_const_decl(z3context, model, i);
      inc_ref(z3context, keyDecl);

      Preconditions.checkArgument(
          get_arity(z3context, keyDecl) == 0, "Declaration is not a constant");

      long var = mk_app(z3context, keyDecl);
      Formula key = creator.encapsulateWithTypeOf(var);

      long value = model_get_const_interp(z3context, model, keyDecl);
      inc_ref(z3context, value);

      long symbol = get_decl_name(z3context, keyDecl);
      Object lValue = creator.convertValue(value);

      // cleanup outdated data
      dec_ref(z3context, keyDecl);
      dec_ref(z3context, value);

      out.add(new ValueAssignment(key, symbolToString(symbol), lValue, ImmutableList.of()));
    }

    // Iterate through function applications.
    for (int funcIdx = 0; funcIdx < model_get_num_funcs(z3context, model); funcIdx++) {
      long funcDecl = model_get_func_decl(z3context, model, funcIdx);
      inc_ref(z3context, funcDecl);

      long symbol = get_decl_name(z3context, funcDecl);

      long interp = model_get_func_interp(z3context, model, funcDecl);
      func_interp_inc_ref(z3context, interp);

      int numInterpretations = func_interp_get_num_entries(z3context, interp);
      for (int interpIdx = 0; interpIdx < numInterpretations; interpIdx++) {
        long entry = func_interp_get_entry(z3context, interp, interpIdx);
        func_entry_inc_ref(z3context, entry);

        Object value = creator.convertValue(func_entry_get_value(z3context, entry));
        int noArgs = func_entry_get_num_args(z3context, entry);
        long[] args = new long[noArgs];
        List<Object> argumentInterpretation = new ArrayList<>();

        for (int k = 0; k < noArgs; k++) {
          long arg = func_entry_get_arg(z3context, entry, k);
          inc_ref(z3context, arg);
          argumentInterpretation.add(creator.convertValue(arg));
          args[k] = arg;
        }
        Formula formula = creator.encapsulateWithTypeOf(mk_app(z3context, funcDecl, args));

        // Clean up memory.
        for (long arg : args) {
          dec_ref(z3context, arg);
        }
        func_entry_dec_ref(z3context, entry);

        out.add(
            new ValueAssignment(formula, symbolToString(symbol), value, argumentInterpretation));
      }
      func_interp_dec_ref(z3context, interp);
      dec_ref(z3context, funcDecl);
    }
    return out.build();
  }

  private String symbolToString(long symbol) {
    switch (get_symbol_kind(z3context, symbol)) {
      case Z3NativeApiConstants.Z3_STRING_SYMBOL:
        return get_symbol_string(z3context, symbol);
      case Z3NativeApiConstants.Z3_INT_SYMBOL:
        return "#" + get_symbol_int(z3context, symbol);
      default:
        throw new AssertionError("Unknown symbol kind " + get_symbol_kind(z3context, symbol));
    }

  }
}
