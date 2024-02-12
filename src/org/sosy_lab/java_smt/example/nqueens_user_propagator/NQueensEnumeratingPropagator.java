// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.example.nqueens_user_propagator;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.PropagatorBackend;
import org.sosy_lab.java_smt.basicimpl.AbstractUserPropagator;

/**
 * This propagator enumerates the solutions of the NQueens problem by raising a conflict whenever
 * the solver finds a model.
 */
public class NQueensEnumeratingPropagator extends AbstractUserPropagator {
  // For backtracking
  protected final Deque<Integer> fixedCount = new ArrayDeque<>();
  protected final Deque<BooleanFormula> fixedVariables = new ArrayDeque<>();
  protected final Map<BooleanFormula, Boolean> currentModel = new HashMap<>();

  // Set of found solutions
  // Implementation note: The hashcodes of the different NQueens models tend to overlap (due to
  // patterns in the models) which degrades the <modelSet>'s performance.
  // So instead, we transform the model before storing it.
  protected final Set<Map<BooleanFormula, Integer>> modelSet = new HashSet<>();

  public int getNumOfSolutions() {
    return modelSet.size();
  }

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
    // We found a model. Note that the solver is allowed to revise a previously found model,
    // so we rely on the uniqueness provided by sets to avoid duplicate counting.
    final Map<BooleanFormula, Integer> transformedModel = new HashMap<>(currentModel.size());
    currentModel.forEach((k, v) -> transformedModel.put(k, k.hashCode() * v.hashCode()));
    modelSet.add(transformedModel);

    // Raise conflict on the whole model to force the solver to find another one.
    // NOTE: It should be sufficient to raise a conflict on only the positive variables.
    getBackend().propagateConflict(fixedVariables.toArray(new BooleanFormula[0]));
  }

  @Override
  public void onKnownValue(BooleanFormula var, boolean value) {
    fixedVariables.push(var);
    currentModel.put(var, value);
  }

  @Override
  public void initializeWithBackend(PropagatorBackend backend) {
    super.initializeWithBackend(backend);
    backend.notifyOnFinalCheck();
    backend.notifyOnKnownValue();
  }
}
