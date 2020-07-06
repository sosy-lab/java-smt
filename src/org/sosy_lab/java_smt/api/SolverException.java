// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import org.checkerframework.checker.nullness.qual.Nullable;

/** Exception thrown if there is an error during SMT solving. */
public class SolverException extends Exception {

  private static final long serialVersionUID = -1557936144555925180L;

  public SolverException(@Nullable String msg) {
    super(msg);
  }

  public SolverException(@Nullable String msg, @Nullable Throwable t) {
    super(msg, t);
  }
}
