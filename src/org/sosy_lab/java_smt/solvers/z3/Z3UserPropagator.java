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
import com.microsoft.z3.Native;
import org.sosy_lab.java_smt.api.PropagatorBackend;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.UserPropagator;

final class Z3UserPropagator extends Native.UserPropagatorBase implements PropagatorBackend {
  private final Z3FormulaCreator creator;
  private final Z3FormulaManager manager;
  private final UserPropagator userPropagator;

  // function calls from z3's side
  // (forwarding callbacks to the user propagator)
  @Override
  public void pushWrapper() {
    userPropagator.onPush();
  }

  @Override
  public void popWrapper(int num) {
    userPropagator.onPop(num);
  }

  @Override
  public void finWrapper() {
    userPropagator.onFinalCheck();
  }

  @Override
  public void eqWrapper(long lx, long ly) {
    userPropagator.onEquality(creator.encapsulateBoolean(lx), creator.encapsulateBoolean(ly));
  }

  // to function correctly, new prop and context are needed
  // currently, there is no support for delegating subproblems to new user propagators
  @Override
  public Z3UserPropagator freshWrapper(long lctx) {
    return this;
  }

  @Override
  public void createdWrapper(long le) {
  }

  @Override
  public void fixedWrapper(long lvar, long lvalue) {
    userPropagator.onKnownValue(creator.encapsulateBoolean(lvar),
        creator.encapsulateBoolean(lvalue));
  }

  public void decideWrapper(long expr, int i, int j) {}


  // function calls from java-smt's side (mostly calls to the smt backend)
  // (register events on z3's side)

  Z3UserPropagator(long ctx, long solver, Z3FormulaCreator creator, Z3FormulaManager manager,
                          UserPropagator userPropagator) {
    super(ctx, solver);
    this.creator = creator;
    this.userPropagator = userPropagator;
    this.manager = manager;
  }

  @Override
  public void registerExpression(BooleanFormula exprToWatch) {
    Native.propagateAdd(this, ctx, solver, javainfo, creator.extractInfo(exprToWatch));
  }

  @Override
  public void propagateConflict(BooleanFormula[] conflictLiterals) {
    propagateConsequence(conflictLiterals, manager.getBooleanFormulaManager().makeFalse());
  }

  @Override
  public void propagateConsequence(BooleanFormula[] assignedLiterals, BooleanFormula consequence) {
    propagateConsequenceWithEqualities(assignedLiterals, new BooleanFormula[0],
        new BooleanFormula[0], consequence);
  }

  @Override
  public void propagateConsequenceWithEqualities(
      BooleanFormula[] assignedLiterals,
      BooleanFormula[] equalitiesLHS,
      BooleanFormula[] equalitiesRHS,
      BooleanFormula consequence) {
    Preconditions.checkArgument(equalitiesLHS.length == equalitiesRHS.length);
    Native.propagateConflict(this, ctx, solver, javainfo, assignedLiterals.length,
        formulaArrayToLong(assignedLiterals)
        , equalitiesLHS.length, formulaArrayToLong(equalitiesLHS), formulaArrayToLong(equalitiesRHS),
        creator.extractInfo(consequence));
  }

  private long[] formulaArrayToLong(BooleanFormula[] formulaArray) {
    long[] formulaInfos = new long[formulaArray.length];
    for (int i = 0; i < formulaArray.length; i++) {
      if (formulaArray[i] != null) {
        formulaInfos[i] = creator.extractInfo(formulaArray[i]);
      }
    }
    return formulaInfos;
  }

  @Override
  public void notifyOnKnownValue() { registerFixed(); }

  @Override
  public void notifyOnEquality() { registerEq(); }

  @Override
  public void notifyOnFinalCheck() { registerFinal(); }
}
