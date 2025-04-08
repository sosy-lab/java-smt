/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.mathsat5;

import org.sosy_lab.java_smt.api.proofs.ProofRule;

class Mathsat5ProofRule implements ProofRule {
  // Most comments are taken from the API Reference: https://mathsat.fbk.eu/apireference.html
  //
  enum Rule implements ProofRule {
    THEORY_LEMMA(), // " representing theory lemmas. They have as children a list of terms that
    // consititute the lemma, plus an optional last element which is a more detailed
    // proof produced by a theory solver."
    RES_CHAIN(), // "representing Boolean resolution chains. The children are an interleaving of
    // proofs and terms, where terms are the pivots for the resolution. For example:
    // "res-chain p1 v p2" represents a resolution step between p1 and p2 on the pivot
    // v"
    CLAUSE_HYP(), // " which are the clauses of the (CNF conversion of the) input problem. They have
    // a list of terms as children"
    NULL() // We introduce this rule because Term Nodes in MathSAT5 do not have a rule associated
  // with them.
  ;

    @Override
    public String getName() {
      return name();
    }
  }

  private String name;

  Mathsat5ProofRule(String pName) {
    name = pName;
  }

  @Override
  public String getName() {
    return name;
  }
}
