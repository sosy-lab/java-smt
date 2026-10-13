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

import com.google.errorprone.annotations.FormatMethod;
import com.google.errorprone.annotations.FormatString;
import java.io.PrintStream;
import org.checkerframework.dataflow.qual.TerminatesExecution;
import org.sosy_lab.common.annotations.SuppressForbidden;
import org.sosy_lab.common.io.IO;

/**
 * Utility class for formatted output and error handling in JavaSMT command-line interface.
 *
 * <p>Provides methods for printing error messages with optional color support.
 */
@SuppressForbidden("System.out in this class is ok")
final class Output {

  private Output() {}

  private static final PrintStream ERROR_OUTPUT = System.err;

  private static final boolean USE_COLORS = IO.mayUseColorForOutput();
  private static final String ERROR_COLOR = "\033[31;1m"; // bold red
  private static final String REGULAR_COLOR = "\033[m";

  @TerminatesExecution
  @FormatMethod
  static RuntimeException fatalError(String msg, Object... args) {
    coloredOutput(ERROR_COLOR, msg, args);
    System.exit(JavaSMTMain.ERROR_EXIT_CODE);
    return new RuntimeException("never reached");
  }

  @FormatMethod
  private static void coloredOutput(String color, @FormatString String msg, Object... args) {
    ERROR_OUTPUT.println();

    if (USE_COLORS) {
      ERROR_OUTPUT.print(color);
    }

    ERROR_OUTPUT.printf(msg, args);

    if (USE_COLORS) {
      ERROR_OUTPUT.print(REGULAR_COLOR);
    }

    ERROR_OUTPUT.println();
  }
}
