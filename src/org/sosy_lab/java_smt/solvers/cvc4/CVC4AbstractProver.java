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
package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import edu.nyu.acsys.CVC4.Result;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverException;

abstract class CVC4AbstractProver<T> implements BasicProverEnvironment<T> {
  protected final CVC4FormulaCreator creator;
  protected final CVC4Environment env;

  protected boolean closed = false;

  protected CVC4AbstractProver(CVC4FormulaCreator pFormulaCreator) {
    creator = pFormulaCreator;
    env = pFormulaCreator.getEnv();
    env.reset(); // Gets a fresh SMTEngine

    createConfig();
  }

  protected abstract CVC4Model getCVC4Model();

  protected void createConfig() {
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    env.push();
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    env.pop();
  }



  @Override
  public CVC4Model getModel() {
    Preconditions.checkState(!closed);
    return CVC4Model.create(creator);
  }


  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    Preconditions.checkState(!closed);
    try (CVC4Model model = getModel()) {
      return model.modelToList();
    }
  }

  @Override
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    Result result = env.checkSat();

    if (result.isUnknown()) {
      if (result.whyUnknown().equals(Result.UnknownExplanation.INTERRUPTED)) {
        throw new InterruptedException();
      } else {
        throw new SolverException(
            "CVC4 returned null or unknown on sat check (" + result.toString() + ")");
      }
    } else {
      if (result.isSat() == Result.Sat.SAT) {
        return false;
      } else if (result.isSat() == Result.Sat.UNSAT) {
        return true;
      } else {
        throw new SolverException("CVC4 returned unknown on sat check");
      }
    }
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    env.delete();
    closed = true;
  }
}
