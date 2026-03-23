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

import java.util.Optional;

/**
 * Annotation for SMTInterpol proof nodes. Represents metadata attached to proof terms in the
 * RESOLUTE proof format, such as :rup, :proves, or axiom annotations.
 */
public interface SmtInterpolProofNodeAnnotation {

  /**
   * Returns the raw key of the annotation as it appears in SMTInterpol.
   *
   * @return the raw annotation key (e.g., ":rup", ":proves", ":named")
   */
  String getRawKey();

  /**
   * Returns the value of the annotation. The value type depends on the annotation.
   *
   * @return the annotation value, or empty if not present
   */
  Optional<Object> getValue();
}
