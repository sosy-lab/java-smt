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

import io.github.cvc5.Pair;
import java.util.HashMap;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;

/**
 * In addition to the enumeration done by {@link NQueensEnumeratingPropagator},
 * this propagator also enforces the queen placement constraints without explicit encoding.
 */
public class NQueensConstraintPropagator extends NQueensEnumeratingPropagator {
  private final BooleanFormula[][] symbols;
  private final HashMap<BooleanFormula, Pair<Integer, Integer>> symbolToCoordinates;
  private final BooleanFormulaManager bmgr;

  public NQueensConstraintPropagator(BooleanFormula[][] symbols, BooleanFormulaManager bmgr) {
    super();
    this.symbols = symbols;
    this.bmgr = bmgr;
    symbolToCoordinates = new HashMap<>();
    fillCoordinateMap();
  }

  private void fillCoordinateMap() {
    for (int i = 0; i < symbols[0].length; i++) {
      for (int j = 0; j < symbols[i].length; j++) {
        symbolToCoordinates.put(symbols[i][j], new Pair<>(i, j));
      }
    }
  }

  @Override
  public void onKnownValue(BooleanFormula var, BooleanFormula value) {
    if (bmgr.isTrue(value)) {
      // Check if the placed queen conflicts with another queen
      Pair<Integer, Integer> coordinates = symbolToCoordinates.get(var);
      for (BooleanFormula other : fixedVariables) {
        BooleanFormula otherValue = currentModel.get(other);
        if (bmgr.isTrue(otherValue)) {
          Pair<Integer, Integer> otherCoordinates = symbolToCoordinates.get(other);

          int x1 = coordinates.first;
          int y1 = coordinates.second;
          int x2 = otherCoordinates.first;
          int y2 = otherCoordinates.second;
          if (x1 == x2 || y1 == y2 || Math.abs(x1 - x2) == Math.abs(y1 - y2)) {
            // We have two queens on the same row, same column, or same diagonal.
            // This is not allowed, so we raise a conflict.
            backend.propagateConflict(new BooleanFormula[] { var, other });
          }
        }
      }
    }

    super.onKnownValue(var, value);
  }

}
