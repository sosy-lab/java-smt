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
import java.math.BigInteger;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.java_smt.api.Formula;
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

// Defines all known field keys used by various Princess proof rules (Certificates and Inferences).
final class PrincessProofFields {

  // Helper method to correctly define a generic ProofFieldKey
  @SuppressWarnings("unchecked")
  private static <T> ProofFieldKey<T> createKey(Class<?> clazz, String name) {
    return new ProofFieldKey<>((Class<T>) clazz, name);
  }

  public static final ProofFieldKey<Formula> CLOSING_CONSTRAINT =
      createKey(Formula.class, "closingConstraint");
  public static final ProofFieldKey<Set<Formula>> LOCAL_ASSUMED_FORMULAS =
      createKey(Set.class, "localAssumedFormulas");
  public static final ProofFieldKey<Set<Formula>> ASSUMED_FORMULAS =
      createKey(Set.class, "assumedFormulas");
  public static final ProofFieldKey<List<Set<Formula>>> LOCAL_PROVIDED_FORMULAS =
      createKey(List.class, "localProvidedFormulas");
  public static final ProofFieldKey<Set<Formula>> LOCAL_BOUND_CONSTANTS =
      createKey(Set.class, "localBoundConstants");
  public static final ProofFieldKey<Set<Formula>> CONSTANTS = createKey(Set.class, "constants");
  public static final ProofFieldKey<Set<Formula>> THEORY_AXIOMS =
      createKey(Set.class, "theoryAxioms");

  // Specialized Certificate Fields (PrincessCertificate)

  public static final ProofFieldKey<Formula> CUT_FORMULA = createKey(Formula.class, "cutFormula");
  public static final ProofFieldKey<Formula> LEFT_FORMULA = createKey(Formula.class, "leftFormula");
  public static final ProofFieldKey<Formula> RIGHT_FORMULA =
      createKey(Formula.class, "rightFormula");
  public static final ProofFieldKey<Boolean> LEMMA_FORMULA = createKey(Boolean.class, "lemma");
  public static final ProofFieldKey<Formula> WEAK_INEQUALITY = createKey(Formula.class, "weakInEq");
  public static final ProofFieldKey<BigInteger> EQ_CASES = createKey(BigInteger.class, "eqCases");
  public static final ProofFieldKey<Formula> ELIM_CONSTANT = createKey(Formula.class, "elimConst");
  public static final ProofFieldKey<List<Formula>> OMEGA_BOUNDS_A =
      createKey(List.class, "boundsA");
  public static final ProofFieldKey<List<Formula>> OMEGA_BOUNDS_B =
      createKey(List.class, "boundsB");
  public static final ProofFieldKey<List<BigInteger>> OMEGA_STRENGTHEN_CASES =
      createKey(List.class, "strengthenCases");
  public static final ProofFieldKey<Formula> LEFT_INEQUALITY = createKey(Formula.class, "leftInEq");
  public static final ProofFieldKey<Formula> RIGHT_INEQUALITY =
      createKey(Formula.class, "rightInEq");

  // Specialized Inference Fields (PrincessInference)
  // LEFT_INEQUALITY and RIGHT_INEQUALITY are reused from above
  public static final ProofFieldKey<Formula> SPLIT_FORMULA =
      createKey(Formula.class, "splitFormula");
  public static final ProofFieldKey<Formula> RESULT = createKey(Formula.class, "result");
  public static final ProofFieldKey<Formula> OLD_SYMBOL = createKey(Formula.class, "oldSymbol");
  public static final ProofFieldKey<Formula> NEW_SYMBOL = createKey(Formula.class, "newSymbol");
  public static final ProofFieldKey<Formula> DEFINING_EQUATION =
      createKey(Formula.class, "definingEquation");
  public static final ProofFieldKey<Boolean> SUBST = createKey(Boolean.class, "subst");
  public static final ProofFieldKey<List<List<Object>>> EQUATIONS =
      createKey(List.class, "equations");
  public static final ProofFieldKey<BigInteger> LEFT_COEFFICIENT =
      createKey(BigInteger.class, "leftCoeff");
  public static final ProofFieldKey<BigInteger> RIGHT_COEFFICIENT =
      createKey(BigInteger.class, "rightCoeff");
  public static final ProofFieldKey<Formula> INEQUALITY = createKey(Formula.class, "inequality");
  public static final ProofFieldKey<Formula> EQUATION = createKey(Formula.class, "equation");
  public static final ProofFieldKey<Formula> DIVISIBILITY =
      createKey(Formula.class, "divisibility");
  public static final ProofFieldKey<Formula> QUANTIFIED_FORMULA =
      createKey(Formula.class, "quantifiedFormula");
  public static final ProofFieldKey<List<Object>> INSTANCE_TERMS =
      createKey(List.class, "instanceTerms");
  public static final ProofFieldKey<Formula> INSTANCE_FORMULA =
      createKey(Formula.class, "instance");
  public static final ProofFieldKey<List<Formula>> DISCHARGED_ATOMS =
      createKey(List.class, "dischargedAtoms");
  public static final ProofFieldKey<Certificate> PARTIAL_CERTIFICATE =
      createKey(Certificate.class, "pCert");
  public static final ProofFieldKey<Object> LEFT_ATOM = createKey(Object.class, "leftAtom");
  public static final ProofFieldKey<Object> RIGHT_ATOM = createKey(Object.class, "rightAtom");
  public static final ProofFieldKey<Set<Formula>> PROVIDED_FORMULAS =
      createKey(Set.class, "providedFormulas");
  public static final ProofFieldKey<List<Object>> NEW_CONSTANTS =
      createKey(List.class, "newConstants");
  public static final ProofFieldKey<Formula> TARGET_LITERAL = createKey(Formula.class, "targetLit");
  public static final ProofFieldKey<Object> THEORY = createKey(Object.class, "theory");
  public static final ProofFieldKey<Formula> AXIOM = createKey(Formula.class, "axiom");
  public static final ProofFieldKey<List> EXPANDED_INFERENCES = createKey(List.class, "expand");
  public static final ProofFieldKey<BigInteger> CONSTANT_DIFF =
      createKey(BigInteger.class, "constantDiff");
  public static final ProofFieldKey<BigInteger> FACTOR = createKey(BigInteger.class, "factor");
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
