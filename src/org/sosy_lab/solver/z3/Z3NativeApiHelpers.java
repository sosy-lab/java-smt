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

import static org.sosy_lab.solver.z3.Z3NativeApi.apply_result_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.apply_result_get_num_subgoals;
import static org.sosy_lab.solver.z3.Z3NativeApi.apply_result_get_subgoal;
import static org.sosy_lab.solver.z3.Z3NativeApi.apply_result_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.goal_assert;
import static org.sosy_lab.solver.z3.Z3NativeApi.goal_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.goal_formula;
import static org.sosy_lab.solver.z3.Z3NativeApi.goal_inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.goal_size;
import static org.sosy_lab.solver.z3.Z3NativeApi.inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_and;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_goal;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_or;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_tactic;
import static org.sosy_lab.solver.z3.Z3NativeApi.tactic_apply;
import static org.sosy_lab.solver.z3.Z3NativeApi.tactic_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.tactic_inc_ref;

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
        dec_ref(z3context, overallResult);
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
   */
  static long applyTactic(long z3context, long pF, String tactic) throws InterruptedException {
    long tacticObject = mk_tactic(z3context, tactic);
    tactic_inc_ref(z3context, tacticObject);

    long goal = mk_goal(z3context, true, false, false);
    goal_inc_ref(z3context, goal);
    goal_assert(z3context, goal, pF);

    long result = tactic_apply(z3context, tacticObject, goal);
    apply_result_inc_ref(z3context, result);

    try {
      return applyResultToAST(z3context, result);
    } finally {
      apply_result_dec_ref(z3context, result);
      goal_dec_ref(z3context, goal);
      tactic_dec_ref(z3context, tacticObject);
    }
  }

  private static long applyResultToAST(long z3context, long applyResult) {
    int subgoalsCount = apply_result_get_num_subgoals(z3context, applyResult);
    long[] goalFormulas = new long[subgoalsCount];

    for (int i = 0; i < subgoalsCount; i++) {
      long subgoal = apply_result_get_subgoal(z3context, applyResult, i);
      goal_inc_ref(z3context, subgoal);
      long subgoalAst = goalToAST(z3context, subgoal);
      inc_ref(z3context, subgoalAst);
      goalFormulas[i] = subgoalAst;
      goal_dec_ref(z3context, subgoal);
    }
    try {
      return goalFormulas.length == 1
          ? goalFormulas[0]
          : mk_or(z3context, goalFormulas.length, goalFormulas);
    } finally {
      for (int i = 0; i < subgoalsCount; i++) {
        dec_ref(z3context, goalFormulas[i]);
      }
    }
  }

  private static long goalToAST(long z3context, long goal) {
    int subgoalFormulasCount = goal_size(z3context, goal);
    long[] subgoalFormulas = new long[subgoalFormulasCount];
    for (int k = 0; k < subgoalFormulasCount; k++) {
      long f = goal_formula(z3context, goal, k);
      inc_ref(z3context, f);
      subgoalFormulas[k] = f;
    }
    try {
      return subgoalFormulas.length == 1
          ? subgoalFormulas[0]
          : mk_and(z3context, subgoalFormulas.length, subgoalFormulas);
    } finally {
      for (int k = 0; k < subgoalFormulasCount; k++) {
        dec_ref(z3context, subgoalFormulas[k]);
      }
    }
  }
}
