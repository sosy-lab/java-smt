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

import static org.sosy_lab.solver.z3.Z3NativeApi.inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_func_decl;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_string_symbol;

import com.google.common.primitives.Longs;

import org.sosy_lab.solver.basicimpl.AbstractFunctionFormulaManager;

import java.util.List;

class Z3FunctionFormulaManager extends AbstractFunctionFormulaManager<Long, Long, Long, Long> {

  private final Z3UnsafeFormulaManager unsafeManager;
  private final long z3context;

  Z3FunctionFormulaManager(Z3FormulaCreator creator, Z3UnsafeFormulaManager unsafeManager) {
    super(creator, unsafeManager);
    this.z3context = creator.getEnv();
    this.unsafeManager = unsafeManager;
  }

  @Override
  protected Long createUninterpretedFunctionCallImpl(Long funcDecl, List<Long> pArgs) {
    long[] args = Longs.toArray(pArgs);
    return unsafeManager.createUIFCallImpl(funcDecl, args);
  }

  @Override
  protected Long declareUninterpretedFunctionImpl(
      String pName, Long returnType, List<Long> pArgTypes) {

    long symbol = mk_string_symbol(z3context, pName);
    long[] sorts = Longs.toArray(pArgTypes);
    long func = mk_func_decl(z3context, symbol, sorts, returnType);
    inc_ref(z3context, func);
    return func;
  }
}
