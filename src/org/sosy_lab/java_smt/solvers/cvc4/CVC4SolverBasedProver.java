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
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.Result;
import java.util.ArrayList;
import java.util.List;
import javax.annotation.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;

public abstract class CVC4SolverBasedProver<T> extends CVC4AbstractProver<T> {
  private final List<Expr> assertedFormulas = new ArrayList<>();

  CVC4SolverBasedProver(CVC4FormulaCreator pFormulaCreator) {
    super(pFormulaCreator);
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    env.push();
  }

  @Nullable
  protected Expr addConstraint0(BooleanFormula pF) {
    Preconditions.checkState(!closed);
    Expr exp = creator.extractInfo(pF);
    env.assertFormula(exp);
    assertedFormulas.add(exp);
    return exp;
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    assertedFormulas.remove(assertedFormulas.size() - 1);
    env.pop();
  }

  @Override
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    Result result = env.checkSat();

    if (result.isNull() || result.isUnknown()) {
      throw new SolverException(
          "CVC4 returned null or unknown on sat check (" + result.toString() + ")");
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

  @Override
  protected CVC4Model getCVC4Model() {
    return getModel();
  }
}
