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

import java.util.Collections;
import java.util.List;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

/**
 * Represents the BRANCH_INFERENCE_CERTIFICATE proof rule. This rule acts as a container for
 * multiple inference rules.
 */
class PrincessBranchCertificate extends PrincessCertificate {

  private final List<PrincessProofRule> inferences;

  PrincessBranchCertificate(List<PrincessProofRule> pInferences) {
    super(Certificate.BRANCH_INFERENCE_CERTIFICATE);
    this.inferences = Collections.unmodifiableList(pInferences);
  }

  /** Internal representation of all external Princess Branch Inference rules. */
  enum BranchInference implements ProofRule {
    ALPHA_INFERENCE,
    ANTI_SYMMETRY_INFERENCE,
    BRANCH_INFERENCE,
    COLUMN_REDUCE_INFERENCE,
    COMBINE_EQUATIONS_INFERENCE,
    COMBINE_INEQUALITIES_INFERENCE,
    DIRECT_STRENGTHEN_INFERENCE,
    DIV_RIGHT_INFERENCE,
    GROUND_INST_INFERENCE,
    MACRO_INFERENCE,
    PARTIAL_CERTIFICATE_INFERENCE,
    PRED_UNIFY_INFERENCE,
    QUANTIFIER_INFERENCE,
    REDUCE_INFERENCE,
    REDUCE_PRED_INFERENCE,
    SIMP_INFERENCE,
    THEORY_AXIOM_INFERENCE;

    @Override
    public String getName() {
      return this.name();
    }
  }

  /** Returns the list of contained inference rules. */
  public List<PrincessProofRule> getInferences() {
    return inferences;
  }
}
