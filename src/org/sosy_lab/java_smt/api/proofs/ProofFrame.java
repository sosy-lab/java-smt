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

public abstract class ProofFrame<T> {
  final T proof;
  int numArgs;
  boolean visited;

  protected ProofFrame(T proof) {
    this.proof = proof;
    this.visited = false;
  }

  public T getProof() {
    return proof;
  }

  public int getNumArgs() {
    return numArgs;
  }

  public boolean getVisited() {
    return visited;
  }

  public void setVisited(boolean visited) {
    this.visited = visited;
  }

  public void setNumArgs(int numArgs) {
    this.numArgs = numArgs;
  }
}
