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
package org.sosy_lab.solver.z3;

import com.google.common.primitives.Longs;
import com.microsoft.z3.Native;

import org.sosy_lab.solver.basicimpl.AbstractUFManager;

import java.util.List;

class Z3UFManager extends AbstractUFManager<Long, Long, Long, Long> {

  private final long z3context;

  Z3UFManager(Z3FormulaCreator creator) {
    super(creator);
    this.z3context = creator.getEnv();
  }

  @Override
  protected Long createUninterpretedFunctionCallImpl(Long funcDecl, List<Long> pArgs) {
    return Native.mkApp(z3context, funcDecl, pArgs.size(), Longs.toArray(pArgs));
  }

  @Override
  protected Long declareUninterpretedFunctionImpl(
      String pName, Long returnType, List<Long> pArgTypes) {

    long symbol = Native.mkStringSymbol(z3context, pName);
    long[] sorts = Longs.toArray(pArgTypes);
    long func = Native.mkFuncDecl(z3context, symbol, sorts.length, sorts, returnType);
    Native.incRef(z3context, func);
    return func;
  }
}
