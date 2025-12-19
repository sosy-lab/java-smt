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

import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.api.proofs.ProofFieldKey;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

/** Base class for all concrete proof rules (certificates and inferences). */
abstract class AbstractPrincessRule implements PrincessProofRule {

  private final ProofRule externalRule;
  protected final Map<ProofFieldKey<?>, Object> specificFields = new HashMap<>();

  protected AbstractPrincessRule(ProofRule pRule) {
    this.externalRule = pRule;
  }

  @Override
  public String getName() {
    return externalRule.getName();
  }

  @Override
  public <T> T getSpecificField(ProofFieldKey<T> key) {
    Object value = specificFields.get(key);

    if (value == null) {
      throw new IllegalArgumentException(
          String.format("Rule '%s' does not contain field: %s", getName(), key));
    }

    return key.getValueType().cast(value);
  }
}
