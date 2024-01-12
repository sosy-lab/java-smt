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

package org.sosy_lab.java_smt.example.nqueens_user_propagator;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractUserPropagator;

import java.util.*;

/**
 * This propagator enumerates the solutions of the Nqueens problem
 * by raising a conflict whenever the solver finds a model.
 */
public class NQueensEnumeratingPropagator extends AbstractUserPropagator {
  // For backtracking
  protected final Deque<Integer> fixedCount = new ArrayDeque<>();
  protected final Deque<BooleanFormula> fixedVariables = new ArrayDeque<>();

  protected final HashMap<BooleanFormula, BooleanFormula> currentModel = new HashMap<>();

  // Set of found solutions
  protected final Set<HashMap<BooleanFormula, BooleanFormula>> modelSet = new HashSet<>();

  public int getNumOfSolutions() { return modelSet.size(); }

  @Override
  public void onPush() {
    fixedCount.push(fixedVariables.size());
  }

  @Override
  public void onPop(int numPoppedLevel) {
    for (int i = 0; i < numPoppedLevel; i++) {
      int lastCount = fixedCount.pop();
      while (fixedVariables.size() > lastCount) {
        currentModel.remove(fixedVariables.pop());
      }
    }
  }

  @Override
  public void onFinalCheck() {
    modelSet.add(currentModel);
    // We found a model. Note that the solver is allowed to revise a previously found model,
    // so we rely on the uniqueness provided by the <modelSet> to avoid duplicate counting.

    // Raise conflict on the whole model to force the solver to find another one.
    // NOTE: It should be sufficient to raise a conflict on only the positive variables.
    backend.propagateConflict(fixedVariables.toArray(new BooleanFormula[0]));
  }

  @Override
  public void onKnownValue(BooleanFormula var, BooleanFormula val) {
    fixedVariables.push(var);
    currentModel.put(var, val);
  }

  @Override
  public void initialize() {
    backend.notifyOnFinalCheck();
    backend.notifyOnKnownValue();
  }
}
