/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.bitwuzla.api;

public abstract class AbstractReference implements Reference {
  protected transient long swigCPtr;
  protected transient boolean swigCMemOwn;

  AbstractReference(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
    TermManager.addReference(this);
  }

  abstract void delete();

  public long getSwigCPtr() {
    return swigCPtr;
  }

  public void close() {
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        delete();
        swigCMemOwn = false;
      }
      swigCPtr = 0;
    }
  }
}