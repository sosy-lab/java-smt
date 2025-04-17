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

/**
 * Stores proof related information and gets stored in a stack when processing proofs. Each frame
 * contains a proof object and the number of arguments it has.
 *
 * @param <T> The type of the proof object.
 */
public abstract class ProofFrame<T> {
  T proof;
  int numArgs = 0;
  boolean visited;

  protected ProofFrame(T proof) {
    this.proof = proof;
    this.visited = false;
  }

  /** Get the proof object. */
  public T getProof() {
    return proof;
  }

  /** Get the number of arguments the proof object has. */
  public int getNumArgs() {
    return numArgs;
  }

  /** Check if the frame has been visited. */
  public boolean isVisited() {
    return visited;
  }

  /** Set the frame as visited. */
  public void setAsVisited(boolean visited) {
    this.visited = visited;
  }

  /** Set the number of arguments the proof object has. */
  public void setNumArgs(int numArgs) {
    this.numArgs = numArgs;
  }

  public void setProof(T proof) {
    this.proof = proof;
  }
}
