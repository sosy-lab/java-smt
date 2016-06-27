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

import com.google.common.base.Preconditions;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import com.microsoft.z3.Native;
import com.microsoft.z3.enumerations.Z3_lbool;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.solver.api.BooleanFormula;

abstract class Z3SolverBasedProver<T> extends Z3AbstractProver<T> {

  protected final long z3solver;

  private int level = 0;

  Z3SolverBasedProver(
      Z3FormulaCreator pCreator, long z3params, ShutdownNotifier pShutdownNotifier) {
    super(pCreator, pShutdownNotifier);

    z3solver = Native.mkSolver(z3context);
    Native.solverIncRef(z3context, z3solver);
    Native.solverSetParams(z3context, z3solver, z3params);
  }

  @Override
  public boolean isUnsat() throws Z3SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    int result = Native.solverCheck(z3context, z3solver);
    shutdownNotifier.shutdownIfNecessary();
    undefinedStatusToException(result);
    return result == Z3_lbool.Z3_L_FALSE.toInt();
  }

  protected final void undefinedStatusToException(int solverStatus) throws Z3SolverException {
    if (solverStatus == Z3_lbool.Z3_L_UNDEF.toInt()) {
      throw new Z3SolverException(
          "Solver returned 'unknown' status, reason: "
              + Native.solverGetReasonUnknown(z3context, z3solver));
    }
  }

  @Override
  protected long getZ3Model() {
    return Native.solverGetModel(z3context, z3solver);
  }

  @CanIgnoreReturnValue
  protected long addConstraint0(BooleanFormula f) {
    Preconditions.checkState(!closed);
    long e = creator.extractInfo(f);
    Native.incRef(z3context, e);
    Native.solverAssert(z3context, z3solver, e);
    Native.decRef(z3context, e);
    return e;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    level++;
    Native.solverPush(z3context, z3solver);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(Native.solverGetNumScopes(z3context, z3solver) >= 1);
    level--;
    Native.solverPop(z3context, z3solver, 1);
  }

  protected int getLevel() {
    return level;
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    Preconditions.checkArgument(
        Native.solverGetNumScopes(z3context, z3solver) >= 0,
        "a negative number of scopes is not allowed");

    while (level > 0) {
      pop();
    }
    Native.solverDecRef(z3context, z3solver);

    closed = true;
  }

  @Override
  public String toString() {
    if (closed) {
      return "Closed Z3Solver";
    }
    return Native.solverToString(z3context, z3solver);
  }
}
