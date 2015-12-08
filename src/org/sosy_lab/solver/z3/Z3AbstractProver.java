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

import static org.sosy_lab.solver.z3.Z3NativeApi.model_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_eval;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_inc_ref;

import com.google.common.base.Preconditions;
import com.google.common.base.Verify;

import org.sosy_lab.solver.Model;
import org.sosy_lab.solver.api.BasicProverEnvironment;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.z3.Z3NativeApi.PointerToLong;


abstract class Z3AbstractProver<T> implements BasicProverEnvironment<T> {
  protected final Z3FormulaManager mgr;
  protected final long z3context;

  protected boolean closed = false;

  protected Z3AbstractProver(Z3FormulaManager mgr) {
    this.mgr = mgr;
    z3context = mgr.getEnvironment();
  }

  protected abstract long getZ3Model();

  @Override
  public Model getModel() {
    Preconditions.checkState(!closed);
    return Z3Model.parseZ3Model(z3context, getZ3Model());
  }

  @Override
  public <E2 extends Formula> E2 evaluate(E2 f) {
    Preconditions.checkState(!closed);
    long z3model = getZ3Model();
    model_inc_ref(z3context, z3model);

    PointerToLong out = new PointerToLong();
    boolean status = model_eval(z3context, z3model, mgr.extractInfo(f), true, out);
    Verify.verify(status, "Error during model evaluation");

    E2 outValue = mgr.getFormulaCreator().encapsulate(
        mgr.getFormulaType(f),
        out.value);

    model_dec_ref(z3context, z3model);
    return outValue;
  }

  @Override
  public T push(BooleanFormula f) {
    Preconditions.checkState(!closed);
    push();
    return addConstraint(f);
  }
}
