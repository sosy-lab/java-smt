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

/** A proof rule from a given proof format. */
public interface ProofRule {

  /** Get the name of the proof rule. */
  String getName();

  /** Get the formula of the proof rule. */
  default String getFormula() {
    return "no formula available";
  }

  /*
   * Get a proof rule from its name.
   *
   * @return A proof rule.

  static <T extends ProofRule> T fromName(Class<T> clazz, String name) {
    ProofRule rule = ProofRuleRegistry.fromName(clazz, name);
    if (rule == null) {
      throw new IllegalArgumentException(
          "Unknown proof rule in " + clazz.getSimpleName() + ": " + name);
    }
    return clazz.cast(rule);
  }
   */
}
