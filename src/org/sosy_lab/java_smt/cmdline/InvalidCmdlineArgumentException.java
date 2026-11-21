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

import java.io.Serial;

/** Exception thrown when an invalid command-line argument is provided. */
public class InvalidCmdlineArgumentException extends Exception {

  @Serial private static final long serialVersionUID = -6526968677815416436L;

  public InvalidCmdlineArgumentException(String pMsg) {
    super(pMsg);
  }

  public InvalidCmdlineArgumentException(String pMsg, Throwable pCause) {
    super(pMsg, pCause);
  }
}
