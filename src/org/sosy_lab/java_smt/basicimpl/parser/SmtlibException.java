/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl.parser;

import java.io.Serial;

public class SmtlibException extends IllegalArgumentException {
  @Serial private static final long serialVersionUID = -5011762550769108967L;

  private final int line;
  private final int column;

  private final String info;

  SmtlibException(String pPrefix, int pLine, int pColumn, String pInfo, Throwable pThrowable) {
    super(format(pPrefix, pLine, pColumn, pInfo), pThrowable);
    line = pLine;
    column = pColumn;
    info = pInfo;
  }

  SmtlibException(String pPrefix, int pLine, int pColumn, String pInfo) {
    super(format(pPrefix, pLine, pColumn, pInfo));
    line = pLine;
    column = pColumn;
    info = pInfo;
  }

  private static String format(String pPrefix, int pLine, int pColumn, String pInfo) {
    return "%s in line %s, column %s:%s%s"
        .formatted(
            pPrefix,
            pLine,
            pColumn,
            pInfo.contains("\n") || pInfo.length() > 100 ? "\n" : " ",
            pInfo);
  }

  public int getLine() {
    return line;
  }

  public int getColumn() {
    return column;
  }

  public String getInfo() {
    return info;
  }
}
