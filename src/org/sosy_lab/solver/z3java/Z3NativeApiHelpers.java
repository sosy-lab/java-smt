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

import com.microsoft.z3.ApplyResult;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Goal;
import com.microsoft.z3.Tactic;

import org.sosy_lab.solver.SolverException;

class Z3NativeApiHelpers {
  private Z3NativeApiHelpers() {}

  /**
   * Apply multiple tactics in sequence.
   * @throws InterruptedException thrown by JNI code in case of termination request
   * @throws SolverException thrown by JNI code in case of error
   */
  static BoolExpr applyTactics(Context z3context, final BoolExpr pF, String... pTactics)
      throws InterruptedException, SolverException {
    BoolExpr overallResult = pF;
    for (String tactic : pTactics) {
      overallResult = applyTactic(z3context, overallResult, tactic);
    }
    return overallResult;
  }

  /**
   * Apply tactic on a Z3_ast object, convert the result back to Z3_ast.
   *
   * @param pContext Z3_context
   * @param tactic Z3 Tactic Name
   * @param pOverallResult Z3_ast
   * @return Z3_ast
   *
   * @throws InterruptedException can be thrown by the native code.
   */
  static BoolExpr applyTactic(Context pContext, BoolExpr pOverallResult, String tactic)
      throws InterruptedException{
    Tactic tacticObject = pContext.mkTactic(tactic);

    Goal goal = pContext.mkGoal(true, false, false);
    goal.add(pOverallResult);

    ApplyResult result = tacticObject.apply(goal);
    return applyResultToAST(pContext, result);
  }

  private static BoolExpr applyResultToAST(Context pContext, ApplyResult pResult) {
    int subgoalsCount = pResult.getNumSubgoals();
    BoolExpr[] goalFormulas = new BoolExpr[subgoalsCount];
    Goal[] subGoals = pResult.getSubgoals();

    for (int i = 0; i < subgoalsCount; i++) {
      goalFormulas[i] = goalToAST(pContext, subGoals[i]);
    }
    return goalFormulas.length == 1 ? goalFormulas[0] : pContext.mkOr(goalFormulas);
  }

  private static BoolExpr goalToAST(Context pContext, Goal pSubGoals) {
    BoolExpr[] subgoalFormulas = pSubGoals.getFormulas();
    return subgoalFormulas.length == 1 ? subgoalFormulas[0] : pContext.mkAnd(subgoalFormulas);
  }
}
