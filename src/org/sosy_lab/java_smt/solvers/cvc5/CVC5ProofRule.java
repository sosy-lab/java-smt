/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.cvc5;

import org.sosy_lab.java_smt.api.proofs.ProofRule;

public enum CVC5ProofRule implements ProofRule {
  ACI_RULE();

  @Override
  public String getName() {
    return "";
  }

  @Override
  public String getFormula() {
    return "";
  }
}
