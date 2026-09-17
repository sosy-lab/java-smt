/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.cmdline;

/** Exception thrown when an invalid command-line argument is provided. */
public class InvalidCmdlineArgumentException extends Exception {

  private static final long serialVersionUID = -6526968677815416436L;

  public InvalidCmdlineArgumentException(final String msg) {
    super(msg);
  }

  public InvalidCmdlineArgumentException(final String msg, final Throwable cause) {
    super(msg, cause);
  }
}
