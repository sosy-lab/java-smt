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
import java.io.IOException;
import java.io.UncheckedIOException;
import org.sosy_lab.common.io.IO;

/**
 * Utility class for output in JavaSMT command-line interface. All output goes to an {@link
 * Appendable}, such that stdout and stderr can be replaced in tests.
 */
final class Output {

  private Output() {}

  private static final boolean USE_COLORS = IO.mayUseColorForOutput();
  private static final String ERROR_COLOR = "\033[31;1m"; // bold red
  private static final String REGULAR_COLOR = "\033[m";

  /** Appends the line and a line separator to the given output. */
  static void println(Appendable out, String line) {
    try {
      out.append(line).append(System.lineSeparator());
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    }
  }

  /**
   * Prints an error message to the given output, in color if the console supports it. This method
   * does not terminate the program, the caller is responsible for returning the exit code.
   *
   * @param err the output for error messages, usually {@link System#err}
   * @param msg the message as format string for {@link String#format}
   * @param args the arguments for the format string
   */
  @FormatMethod
  static void error(Appendable err, @FormatString String msg, Object... args) {
    String message = String.format(msg, args);
    println(err, "");
    println(err, USE_COLORS ? ERROR_COLOR + message + REGULAR_COLOR : message);
  }
}
