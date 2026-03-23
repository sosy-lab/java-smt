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

import java.util.Optional;
import org.sosy_lab.java_smt.api.proofs.SmtInterpolProofNodeAnnotation;

/**
 * Factory for creating {@link SmtInterpolProofNodeAnnotation} instances.
 */
final class SmtInterpolProofNodeAnnotationFactory {

  private SmtInterpolProofNodeAnnotationFactory() {}

  /**
   * Creates an annotation.
   *
   * @param rawKey the raw annotation key (e.g., ":rup", ":proves", ":pivot")
   * @param value the annotation value
   * @return a new annotation
   */
  static SmtInterpolProofNodeAnnotation create(String rawKey, Object value) {
    return new SmtInterpolProofNodeAnnotationImpl(rawKey, Optional.ofNullable(value));
  }
}
