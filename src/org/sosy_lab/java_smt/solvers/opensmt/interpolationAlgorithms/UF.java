/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.opensmt.interpolationAlgorithms;

public enum UF {
  STRONG(0),
  WEAK(2),
  RANDOM(3);

  private final int value;

  UF(int i) {
    value = i;
  }

  public int getValue() {
    return value;
  }
}
