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
package org.sosy_lab.solver.z3java;

import com.google.common.base.Preconditions;
import com.google.common.collect.UnmodifiableIterator;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Sort;
import com.microsoft.z3.StringSymbol;
import com.microsoft.z3.Symbol;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.basicimpl.AbstractModel;

import java.util.Iterator;

import javax.annotation.Nullable;

class Z3Model extends AbstractModel<Expr, Sort, Context> {

  private final com.microsoft.z3.Model model;
  private final Context z3context;

  @SuppressWarnings("hiding")
  private final Z3FormulaCreator creator;

  Z3Model(Context pZ3context, com.microsoft.z3.Model pModel, Z3FormulaCreator pCreator) {
    super(pCreator);
    model = pModel;
    this.z3context = pZ3context;
    creator = pCreator;
  }

  public static Model parseZ3Model(
      Context z3context, com.microsoft.z3.Model z3model, Z3FormulaCreator pCreator) {
    return new Z3Model(z3context, z3model, pCreator);
  }

  @Nullable
  @Override
  public Object evaluateImpl(Expr f) {
    return creator.convertValue(model.eval(f, true));
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
      numConsts = model.getNumConsts();
    }

    @Override
    public boolean hasNext() {
      return cursor != numConsts;
    }

    @Override
    public ValueAssignment next() {
      FuncDecl keyDecl = model.getConstDecls()[cursor++];

      Preconditions.checkArgument(keyDecl.getArity() == 0, "Declaration is not a constant");

      Expr var = z3context.mkApp(keyDecl);
      Formula key = creator.encapsulateWithTypeOf(var);
      Expr value = model.getConstInterp(keyDecl);
      Symbol symbol = var.getFuncDecl().getName();

      Preconditions.checkArgument(
          symbol instanceof StringSymbol,
          "Given symbol of expression is no stringSymbol! (%s)",
          var);

      Object lValue = creator.convertValue(value);

      return new ValueAssignment(key, lValue);
    }
  }

  @Override
  public String toString() {
    return model.toString();
  }
}
