// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

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
  public void onKnownValue(BooleanFormula var, BooleanFormula value) {
    fixedVariables.push(var);
    currentModel.put(var, value);
  }

  @Override
  public void initialize() {
    backend.notifyOnFinalCheck();
    backend.notifyOnKnownValue();
  }
}
