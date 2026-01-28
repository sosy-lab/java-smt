/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.api.proofs;

/**
 * A proof rule from a given proof format. E.g.:
 *
 * <p>CVC5 currently uses many rules in its calculus for proving unsatisfiability. Through its API
 * one can retrieve a rule in form of an enum. See: <a
 * href="https://cvc5.github.io/docs/cvc5-1.3.2/api/java/io/github/cvc5/ProofRule.html">...</a>
 * Note: Other solvers may return just a String, the name of the rule applied.
 *
 * <p>We can look at RESOLUTION: Given two nodes viewed as clauses C_1 and C_2, as well as the pivot
 * which is a literal occurring in C_1 and C_2 (positively and negatively or the other way around)
 * and its polarity, it produces C which "is a clause resulting from collecting all the literals in
 * C_1, minus the first occurrence of the pivot or its negation, and C_2, minus the first occurrence
 * of the pivot or its negation, according to the policy above". See the link given earlier.
 */
public interface ProofRule {

  /** Get the name of the proof rule. */
  String getName();
}
