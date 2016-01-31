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

import com.google.common.base.Preconditions;

import org.sosy_lab.solver.api.BasicProverEnvironment;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.basicimpl.Model;

abstract class Z3AbstractProver<T> implements BasicProverEnvironment<T> {
  protected final Z3FormulaCreator creator;
  protected final long z3context;

  protected boolean closed = false;

  protected Z3AbstractProver(Z3FormulaCreator creator) {
    this.creator = creator;
    z3context = creator.getEnv();
  }

  protected abstract long getZ3Model();

  @Override
  public Model getModel() {
    Preconditions.checkState(!closed);
    return new Z3Model(z3context, getZ3Model(), creator);
  }

  @Override
  public T push(BooleanFormula f) {
    Preconditions.checkState(!closed);
    push();
    return addConstraint(f);
  }
}
