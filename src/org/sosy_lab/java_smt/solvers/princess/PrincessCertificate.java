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

/** Represents all simple Princess proof certificates (e.g., BETA, BINARY, CUT). */
class PrincessCertificate extends AbstractPrincessRule {

  /** Internal representation of all external Princess Certificate rules. */
  enum Certificate implements ProofRule {
    BETA_CERTIFICATE,
    BINARY_CERTIFICATE,
    BRANCH_INFERENCE_CERTIFICATE,
    CLOSE_CERTIFICATE,
    CUT_CERTIFICATE,
    OMEGA_CERTIFICATE,
    PARTIAL_CERTIFICATE,
    SPLIT_EQ_CERTIFICATE,
    STRENGTHEN_CERTIFICATE;

    @Override
    public String getName() {
      return this.name();
    }
  }

  PrincessCertificate(ProofRule pRule) {
    super(pRule);
  }
}
