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

import ap.proof.certificates.Certificate;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

public interface PrincessProofRule extends ProofRule {

  // Retrieves a rule-specific field's value
  <T> T getSpecificField(ProofFieldKey<T> key);
}

// A type-safe key used for storing and retrieving rule-specific fields in a heterogeneous
// container.
class ProofFieldKey<T> {
  private final Class<T> valueType;
  private final String externalFieldName;

  public ProofFieldKey(Class<T> valueType, String externalFieldName) {
    this.valueType = valueType;
    this.externalFieldName = externalFieldName;
  }

  public Class<T> getValueType() {
    return valueType;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    ProofFieldKey<?> that = (ProofFieldKey<?>) o;
    return valueType.equals(that.valueType) && externalFieldName.equals(that.externalFieldName);
  }

  @Override
  public int hashCode() {
    return 31 * valueType.hashCode() + externalFieldName.hashCode();
  }

  @Override
  public String toString() {
    return String.format("%s (%s)", externalFieldName, valueType.getSimpleName());
  }
}

// Base class for all concrete proof rules (certificates and inferences).
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

// Represents all simple Princess proof certificates (e.g., BETA, BINARY, CUT).
class PrincessCertificate extends AbstractPrincessRule {

  // Internal representation of all external Princess Certificate rules.
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

// Represents the BRANCH_INFERENCE_CERTIFICATE proof rule. This rule acts as a container for
// multiple inference rules.
class PrincessBranchCertificate extends PrincessCertificate {

  private final List<PrincessProofRule> inferences;

  PrincessBranchCertificate(List<PrincessProofRule> pInferences) {
    super(Certificate.BRANCH_INFERENCE_CERTIFICATE);
    this.inferences = Collections.unmodifiableList(pInferences);
  }

  // Internal representation of all external Princess Branch Inference rules.
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

  // Returns the list of contained inference rules.
  public List<PrincessProofRule> getInferences() {
    return inferences;
  }
}

// Represents all simple Princess branch inferences (e.g., ALPHA_INFERENCE, REDUCE_INFERENCE).
class PrincessInference extends AbstractPrincessRule {

  PrincessInference(ProofRule pRule) {
    super(pRule);
  }
}
