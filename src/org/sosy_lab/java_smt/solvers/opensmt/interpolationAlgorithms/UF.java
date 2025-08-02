/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.opensmt.interpolationAlgorithms;

/**
 * Enumeration for the different algorithms for UF interpolation.
 *
 * <p>For details, please see the original sources:
 * https://github.com/usi-verification-and-security/opensmt/blob/c267e01e1e0d4d4b7f9ba273dd910c070c1aa9b1/src/options/SMTConfig.h#L169-L171
 */
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
