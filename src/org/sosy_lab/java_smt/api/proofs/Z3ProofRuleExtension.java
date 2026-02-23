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

import com.google.common.collect.ImmutableList;

/**
 * This is an extension interface for interacting with Z3 proof rule specific methods. E.g. some
 * proof rules include optional "parameters", these add information about the proof rule. One of
 * them is the TH_LEMMA rule:
 *
 * <p>- Z3_OP_PR_TH_LEMMA: Generic proof for theory lemmas. The theory lemma function comes with one
 * or more parameters. The first parameter indicates the name of the theory. For the theory of
 * arithmetic, additional parameters provide hints for checking the theory lemma. The hints for
 * arithmetic are:
 *
 * <p>- farkas - followed by rational coefficients. Multiply the coefficients to the inequalities in
 * the lemma, add the (negated) inequalities and obtain a contradiction.
 *
 * <p>- triangle-eq - Indicates a lemma related to the equivalence:
 *
 * <p>(iff (= t1 t2) (and (<= t1 t2) (<= t2 t1)))
 *
 * <p>- gcd-test - Indicates an integer linear arithmetic lemma that uses a gcd test.
 *
 * <p>As other solvers do not work in this way, an extension specifically for Z3 is provided.
 */
public interface Z3ProofRuleExtension {
  ImmutableList<Z3ProofRuleParameter<?>> getParameters();
}
