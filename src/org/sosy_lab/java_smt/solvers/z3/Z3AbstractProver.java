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
package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverException;

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
  public Z3Model getModel() {
    Preconditions.checkState(!closed);
    return Z3Model.create(z3context, getZ3Model(), creator);
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    Preconditions.checkState(!closed);
    try (Z3Model model = getModel()) {
      return model.modelToList();
    }
  }
}
