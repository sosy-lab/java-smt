/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.api.proofs;

import org.sosy_lab.java_smt.solvers.princess.PrincessProofFields;

/**
 * A type-safe key used for storing and retrieving rule-specific fields. This should allow to store
 * information provided by the solver's proof object. Methods for retrieving the type and external
 * name of the attributes are provided. Instances of this class are meant to be used in a map as
 * keys and the value of the field, retrieved from a given solver as the value. See {@link
 * PrincessProofFields}
 */
public abstract class ProofFieldKey<T> {
  private final Class<T> valueType;
  private final String externalFieldName;

  public ProofFieldKey(Class<T> valueType, String externalFieldName) {
    this.valueType = valueType;
    this.externalFieldName = externalFieldName;
  }

  public Class<T> getValueType() {
    return valueType;
  }

  public String getExternalFieldName() {
    return externalFieldName;
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
