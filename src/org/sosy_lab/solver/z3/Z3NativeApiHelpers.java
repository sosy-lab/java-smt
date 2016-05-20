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

import com.microsoft.z3.Native;
import com.microsoft.z3.Z3Exception;

import org.sosy_lab.solver.SolverException;

class Z3NativeApiHelpers {
  private Z3NativeApiHelpers() {}

  /**
   * Apply multiple tactics in sequence.
   * @throws InterruptedException thrown by JNI code in case of termination request
   * @throws SolverException thrown by JNI code in case of error
   */
  static long applyTactics(long z3context, final Long pF, String... pTactics)
      throws InterruptedException, SolverException {
    long overallResult = pF;
    for (String tactic : pTactics) {
      long tacticResult = applyTactic(z3context, overallResult, tactic);
      if (overallResult != pF) {
        Native.decRef(z3context, overallResult);
      }
      overallResult = tacticResult;
    }
    return overallResult;
  }

  /**
   * Apply tactic on a Z3_ast object, convert the result back to Z3_ast.
   *
   * @param z3context Z3_context
   * @param tactic Z3 Tactic Name
   * @param pF Z3_ast
   * @return Z3_ast
   *
   * @throws InterruptedException If execution gets interrupted.
   */
  static long applyTactic(long z3context, long pF, String tactic) throws InterruptedException {
    long tacticObject = Native.mkTactic(z3context, tactic);
    Native.tacticIncRef(z3context, tacticObject);

    long goal = Native.mkGoal(z3context, true, false, false);
    Native.goalIncRef(z3context, goal);
    Native.goalAssert(z3context, goal, pF);

    long result;
    try {
      result = Native.tacticApply(z3context, tacticObject, goal);
    } catch (Z3Exception exp) {
      if (exp.getMessage().equals("canceled")) {
        throw new InterruptedException("Z3 Calculation cancelled");
      }
      throw exp;
    }
    Native.applyResultIncRef(z3context, result);

    try {
      return applyResultToAST(z3context, result);
    } finally {
      Native.applyResultDecRef(z3context, result);
      Native.goalDecRef(z3context, goal);
      Native.tacticDecRef(z3context, tacticObject);
    }
  }

  private static long applyResultToAST(long z3context, long applyResult) {
    int subgoalsCount = Native.applyResultGetNumSubgoals(z3context, applyResult);
    long[] goalFormulas = new long[subgoalsCount];

    for (int i = 0; i < subgoalsCount; i++) {
      long subgoal = Native.applyResultGetSubgoal(z3context, applyResult, i);
      Native.goalIncRef(z3context, subgoal);
      long subgoalAst = goalToAST(z3context, subgoal);
      Native.incRef(z3context, subgoalAst);
      goalFormulas[i] = subgoalAst;
      Native.goalDecRef(z3context, subgoal);
    }
    try {
      return goalFormulas.length == 1
          ? goalFormulas[0]
          : Native.mkOr(z3context, goalFormulas.length, goalFormulas);
    } finally {
      for (int i = 0; i < subgoalsCount; i++) {
        Native.decRef(z3context, goalFormulas[i]);
      }
    }
  }

  private static long goalToAST(long z3context, long goal) {
    int subgoalFormulasCount = Native.goalSize(z3context, goal);
    long[] subgoalFormulas = new long[subgoalFormulasCount];
    for (int k = 0; k < subgoalFormulasCount; k++) {
      long f = Native.goalFormula(z3context, goal, k);
      Native.incRef(z3context, f);
      subgoalFormulas[k] = f;
    }
    try {
      return subgoalFormulas.length == 1
          ? subgoalFormulas[0]
          : Native.mkAnd(z3context, subgoalFormulas.length, subgoalFormulas);
    } finally {
      for (int k = 0; k < subgoalFormulasCount; k++) {
        Native.decRef(z3context, subgoalFormulas[k]);
      }
    }
  }
}
