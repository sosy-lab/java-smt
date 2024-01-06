// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

/* Base class for everything in the debugging.* package. Provides a method that makes sure that API
 * calls are only made from the same thread that was used to create the object.
 */

import com.google.common.base.Preconditions;

public class ThreadChecks {
  private final Thread localThread = Thread.currentThread();

  /** Assert that this object is only used by the thread that created it. */
  public void assertThreadLocal() {
    Thread currentThread = Thread.currentThread();
    Preconditions.checkArgument(
        currentThread.equals(localThread),
        "Solver object was not defined " + "by this thread. " + "Defined on %s, but this is %s.",
        localThread.getName(),
        currentThread.getName());
  }
}
