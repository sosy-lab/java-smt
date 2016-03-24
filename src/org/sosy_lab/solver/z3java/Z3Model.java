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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableList.Builder;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.FuncInterp;
import com.microsoft.z3.Sort;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.basicimpl.AbstractModel;

import java.util.Iterator;
import java.util.List;

import javax.annotation.Nullable;

class Z3Model extends AbstractModel<Expr, Sort, Context> {

  private final com.microsoft.z3.Model model;
  private final ImmutableList<BooleanFormula> trackedConstraints;
  private @Nullable List<ValueAssignment> assignments = null;

  @SuppressWarnings("hiding")
  private final Z3FormulaCreator creator;

  Z3Model(
      com.microsoft.z3.Model pModel,
      Z3FormulaCreator pCreator,
      List<BooleanFormula> pTrackedConstraints) {
    super(pCreator);
    model = pModel;
    creator = pCreator;
    trackedConstraints = ImmutableList.copyOf(pTrackedConstraints);
  }

  @Nullable
  @Override
  public Object evaluateImpl(Expr f) {
    Expr value = model.eval(f, false);
    if (value.isAlgebraicNumber() || value.isTrue() || value.isFalse() || value.isNumeral()) {
      return creator.convertValue(value);
    }

    // Unfortunately, no other way to detect partial models.
    return null;
  }

  @Override
  public Iterator<ValueAssignment> iterator() {
    if (assignments == null) {
      assignments = modelToList();
    }
    return assignments.iterator();
  }

  private List<ValueAssignment> modelToList() {
    Builder<ValueAssignment> out = ImmutableList.builder();
    for (FuncDecl constDecl : model.getConstDecls()) {
      Expr value = model.getConstInterp(constDecl);
      assert constDecl.getArity() == 0;
      Formula key = creator.encapsulateWithTypeOf(constDecl.apply());
      String name = constDecl.getName().toString();
      out.add(new ValueAssignment(
          key,
          name,
          creator.convertValue(value),
          ImmutableList.of()
      ));
    }

    for (FuncDecl funcDecl : model.getFuncDecls()) {
      FuncInterp interp = model.getFuncInterp(funcDecl);
      String funcName = funcDecl.getName().toString();
      for (FuncInterp.Entry valueEntry : interp.getEntries()) {
        ImmutableList.Builder<Object> args = ImmutableList.builder();
        for (Expr arg : valueEntry.getArgs()) {
          args.add(creator.convertValue(arg));
        }
        Object value = creator.convertValue(valueEntry.getValue());
        Formula f = creator.encapsulateWithTypeOf(funcDecl.apply(valueEntry.getArgs()));
        out.add(new ValueAssignment(
           f, funcName,  value, args.build()
        ));
      }
    }
    return out.build();
  }

  @Override
  public String toString() {
    return model.toString();
  }
}
