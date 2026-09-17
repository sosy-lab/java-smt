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
import org.sosy_lab.common.io.IO;

/**
 * Utility class for formatted output and error handling in JavaSMT command-line interface.
 *
 * <p>Provides methods for printing error messages with optional color support.
 */
final class Output {

  private Output() {}

  private static final boolean USE_COLORS = IO.mayUseColorForOutput();
  private static final String ERROR_COLOR = "\033[31;1m"; // bold red
  private static final String REGULAR_COLOR = "\033[m";

  /**
   * Prints an error message to the given stream. This method does not terminate the program, the
   * caller is responsible for returning the appropriate exit code.
   *
   * @param err the stream for error messages, usually {@link System#err}
   * @param msg the message as format string for {@link PrintStream#printf}
   * @param args the arguments for the format string
   */
  @FormatMethod
  static void error(PrintStream err, @FormatString String msg, Object... args) {
    err.println();

    if (USE_COLORS) {
      err.print(ERROR_COLOR);
    }

    err.printf(msg, args);

    if (USE_COLORS) {
      err.print(REGULAR_COLOR);
    }

    err.println();
  }
}
