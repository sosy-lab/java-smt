/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.princess;

import org.sosy_lab.java_smt.api.proofs.ProofFieldKey;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

public interface PrincessProofRule extends ProofRule {

  // Retrieves a rule-specific field's value
  <T> T getSpecificField(ProofFieldKey<T> key);
}
