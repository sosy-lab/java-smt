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
import org.sosy_lab.java_smt.api.proofs.ProofRule;

public class PrincessProofRule implements ProofRule {

  // In the princess API, its proof calculus is implemented in such a way that the proof rules may
  // show up as certificates or inferences.

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

  enum Inference implements ProofRule {
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

  class Field<T> {
    private final T type;
    private final String name;

    Field(T type, String name) {
      this.type = type;
      this.name = name;
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj) return true;
      if (obj == null || getClass() != obj.getClass()) return false;
      Field<?> other = (Field<?>) obj;
      return type.equals(other.type) && name.equals(other.name);
    }

    @Override
    public int hashCode() {
      return 31 * type.hashCode() + name.hashCode();
    }
  }

  class Value<T> {
    private final T value;

    Value(Field<T> field, T value) {
      this.value = value;
    }

    public T getValue() {
      return value;
    }
  }

  ProofRule rule;
  // The different inference and certificate instances have different fields, this allows to store
  // all of them independently of type
  HashMap<Field<?>, Value<?>> fields = new HashMap<>();

  PrincessProofRule(ProofRule pRule) {
    rule = pRule;
  }

  @Override
  public String getName() {
    return "";
  }
}
