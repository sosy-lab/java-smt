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

abstract class AbstractReference implements Reference {
  protected long swigCPtr;
  protected boolean swigCMemOwn;

  AbstractReference(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
    TermManager.addReference(this);
  }

  /** Delete the native object. **/
  abstract void deleteCPtr();

  @Override
  public synchronized void close() {
    if (swigCPtr != 0) {
      TermManager.removeReference(this);
      if (swigCMemOwn) {
        swigCMemOwn = false;
        deleteCPtr();
      }
      swigCPtr = 0;
    }
  }
}