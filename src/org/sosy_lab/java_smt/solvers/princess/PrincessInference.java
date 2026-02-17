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

import org.sosy_lab.java_smt.api.proofs.ProofRule;

/** Represents all simple Princess branch inferences (e.g., ALPHA_INFERENCE, REDUCE_INFERENCE). */
class PrincessInference extends AbstractPrincessRule {

  PrincessInference(ProofRule pRule) {
    super(pRule);
  }
}
