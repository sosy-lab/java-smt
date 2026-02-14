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
 * This class provides a proof of unsatisifabilty for a given query. It allows the retrieval of the
 * root proof node in the proof DAG.
 */
public interface Proof {

  /**
   * Returns the root proof node of the DAG from this proof.
   *
   * @return an object of type {@link ProofNode} the root proof node.
   * @see ProofNode
   */
  public ProofNode getProofRoot();
}
