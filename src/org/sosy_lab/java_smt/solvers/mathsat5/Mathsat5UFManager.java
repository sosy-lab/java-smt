/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_declare_function;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_function_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_uf;

import com.google.common.primitives.Longs;

import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;

import java.util.List;

class Mathsat5UFManager extends AbstractUFManager<Long, Long, Long, Long> {

  private final long mathsatEnv;

  Mathsat5UFManager(Mathsat5FormulaCreator pCreator) {
    super(pCreator);
    this.mathsatEnv = pCreator.getEnv();
  }

  public long createUIFCallImpl(long funcDecl, long[] args) {
    return msat_make_uf(mathsatEnv, funcDecl, args);
  }

  @Override
  protected Long createUninterpretedFunctionCallImpl(Long funcDecl, List<Long> pArgs) {
    long[] args = Longs.toArray(pArgs);
    return createUIFCallImpl(funcDecl, args);
  }

  @Override
  protected Long declareUninterpretedFunctionImpl(
      String pName, Long returnType, List<Long> pArgTypes) {
    long[] types = Longs.toArray(pArgTypes);
    return createFunctionImpl(pName, returnType, types);
  }

  public long createFunctionImpl(String pName, long returnType, long[] msatTypes) {
    long msatFuncType = msat_get_function_type(mathsatEnv, msatTypes, msatTypes.length, returnType);
    long decl = msat_declare_function(mathsatEnv, pName, msatFuncType);
    return decl;
  }
}
