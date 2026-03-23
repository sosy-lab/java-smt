/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.base.Preconditions;
import java.util.Objects;
import java.util.Optional;
import org.sosy_lab.java_smt.api.proofs.SmtInterpolProofNodeAnnotation;

/**
 * Immutable implementation of {@link SmtInterpolProofNodeAnnotation}.
 *
 * <p>Instances of this class represent a single annotation on a proof term in the SMTInterpol
 * RESOLUTE proof format.
 */
final class SmtInterpolProofNodeAnnotationImpl implements SmtInterpolProofNodeAnnotation {

  private final String rawKey;
  private final Optional<Object> value;

  SmtInterpolProofNodeAnnotationImpl(String pRawKey, Optional<Object> pValue) {
    this.rawKey = Preconditions.checkNotNull(pRawKey);
    this.value = Preconditions.checkNotNull(pValue);
  }

  @Override
  public String getRawKey() {
    return rawKey;
  }

  @Override
  public Optional<Object> getValue() {
    return value;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (!(o instanceof SmtInterpolProofNodeAnnotation)) {
      return false;
    }
    SmtInterpolProofNodeAnnotation that = (SmtInterpolProofNodeAnnotation) o;
    return rawKey.equals(that.getRawKey()) && Objects.equals(value, that.getValue());
  }

  @Override
  public int hashCode() {
    return Objects.hash(rawKey, value);
  }

  @Override
  public String toString() {
    return "SmtInterpolProofNodeAnnotationImpl{"
        + "rawKey='"
        + rawKey
        + '\''
        + ", value="
        + value
        + '}';
  }
}
