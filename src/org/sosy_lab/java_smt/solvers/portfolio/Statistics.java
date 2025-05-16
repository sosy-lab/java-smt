/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import java.io.PrintStream;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.solvers.portfolio.StatisticsUtils.AbstractStatValue;

// TODO: ask Philipp to move this to commons.
/** A class to output statistics and results of an analysis. */
public interface Statistics {

  /**
   * Prints this group of statistics using the given PrintStream.
   *
   * @param out the PrintStream to use for printing the statistics
   */
  void printStatistics(PrintStream out);

  /**
   * Define a name for this group of statistics. May be null, in this case no headings is printed
   * and {@link #printStatistics(PrintStream)} should not actually write to the PrintStream (but may
   * still write output files for example).
   *
   * @return A String with a human-readable name or null.
   */
  @Nullable String getName();

  int DEFAULT_OUTPUT_NAME_COL_WIDTH = 50;

  /**
   * Pretty print with zero indentation
   *
   * @see #put(PrintStream, int, String, Object)
   */
  default void put(PrintStream pTarget, String pName, Object pValue) {
    put(pTarget, 0, pName, pValue);
  }

  /**
   * Print a statistics line in a "pretty" fashion.
   *
   * @param target Write to this stream
   * @param indentLevel Indentation level (0 = no indentation)
   * @param name Left hand side (name/description)
   * @param value Right hand side (value)
   */
  default void put(PrintStream target, int indentLevel, String name, Object value) {
    StatisticsUtils.write(target, indentLevel, DEFAULT_OUTPUT_NAME_COL_WIDTH, name, value);
  }

  default void put(PrintStream target, int indentLevel, AbstractStatValue stat) {
    StatisticsUtils.write(target, indentLevel, DEFAULT_OUTPUT_NAME_COL_WIDTH, stat);
  }
}
