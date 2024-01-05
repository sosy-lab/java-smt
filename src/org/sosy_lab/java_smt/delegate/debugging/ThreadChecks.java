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

import static com.google.common.truth.Truth.assertWithMessage;

public class ThreadChecks {
  private final String localThread = Thread.currentThread().getName();

  /** Assert that this object is only used by the thread that created it. */
  public void assertThreadLocal() {
    assertWithMessage("Solver object was not defined by this thread.")
        .that(Thread.currentThread().getName())
        .isEqualTo(localThread);
  }
}
