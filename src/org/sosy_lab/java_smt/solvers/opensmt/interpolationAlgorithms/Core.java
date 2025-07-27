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

public enum Core {
  MCMILLAN(0),
  PUDLAK(1),
  MCMILLAN_PRIME(2),
  PROOF_SENSITIVE(3),
  PROOF_SENSITIVE_WEAK(4),
  PROOF_SENSITIVE_STRONG(5);

  private final int value;

  Core(int i) {
    value = i;
  }

  public int getValue() {
    return value;
  }
}
