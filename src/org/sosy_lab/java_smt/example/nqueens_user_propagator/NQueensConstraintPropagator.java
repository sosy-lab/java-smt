// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.example.nqueens_user_propagator;

import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.api.BooleanFormula;

/**
 * In addition to the enumeration done by {@link NQueensEnumeratingPropagator}, this propagator also
 * enforces the queen placement constraints without explicit encoding.
 */
public class NQueensConstraintPropagator extends NQueensEnumeratingPropagator {

  private static class Coordinates {
    final int x;
    final int y;

    private Coordinates(int pX, int pY) {
      x = pX;
      y = pY;
    }
  }

  private final BooleanFormula[][] symbols;
  private final Map<BooleanFormula, Coordinates> symbolToCoordinates;

  public NQueensConstraintPropagator(BooleanFormula[][] symbols) {
    this.symbols = symbols;
    symbolToCoordinates = new HashMap<>();
    fillCoordinateMap();
  }

  private void fillCoordinateMap() {
    for (int i = 0; i < symbols[0].length; i++) {
      for (int j = 0; j < symbols[i].length; j++) {
        symbolToCoordinates.put(symbols[i][j], new Coordinates(i, j));
      }
    }
  }

  @Override
  public void onKnownValue(BooleanFormula var, boolean value) {
    if (value) {
      // Check if the placed queen conflicts with another queen
      Coordinates coordinates = symbolToCoordinates.get(var);
      for (BooleanFormula other : fixedVariables) {
        if (currentModel.get(other)) {
          Coordinates otherCoordinates = symbolToCoordinates.get(other);

          int x1 = coordinates.x;
          int y1 = coordinates.y;
          int x2 = otherCoordinates.x;
          int y2 = otherCoordinates.y;
          if (x1 == x2 || y1 == y2 || Math.abs(x1 - x2) == Math.abs(y1 - y2)) {
            // We have two queens on the same row, same column, or same diagonal.
            // This is not allowed, so we raise a conflict.
            getBackend().propagateConflict(new BooleanFormula[] {var, other});
          }
        }
      }
    }

    super.onKnownValue(var, value);
  }
}
