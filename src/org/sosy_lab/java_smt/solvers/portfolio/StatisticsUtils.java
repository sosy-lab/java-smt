/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import com.google.common.base.Strings;
import java.io.PrintStream;
import java.util.logging.Level;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.time.TimeSpan;
import org.sosy_lab.common.time.Timer;

// TODO: ask Philipp to move this to commons.
public class StatisticsUtils {

  private static final TimeSpan STATISTICS_WARNING_TIME = TimeSpan.ofSeconds(10);

  private StatisticsUtils() {}

  public static String toPercent(double val, double full) {
    return String.format("%1.0f%%", val / full * 100);
  }

  public static String toPercent(long val, long full) {
    // cast from long to double looses precision, but is ok for statistics
    return toPercent((double) val, (double) full);
  }

  public static String valueWithPercentage(Number value, Number totalCount) {
    return value + " (" + toPercent(value.doubleValue(), totalCount.doubleValue()) + ")";
  }

  public static String div(double val, double full) {
    return String.format("%.2f", val / full);
  }

  public static String div(long val, long full) {
    // cast from long to double looses precision, but is ok for statistics
    return div((double) val, (double) full);
  }

  public static void write(
      PrintStream target, int indentLevel, int outputNameColWidth, String name, Object value) {
    String indentation = "  ".repeat(indentLevel);
    target.println(
        String.format("%-" + outputNameColWidth + "s %s", indentation + name + ":", value));
  }

  public static void write(
      PrintStream target, int indentLevel, int outputNameColWidth, AbstractStatValue stat) {
    write(target, indentLevel, outputNameColWidth, stat.getTitle(), stat.toString());
  }

  /**
   * This method calls {@link Statistics#printStatistics(PrintStream)} but additionally prints the
   * title and handles cases like statistics that take too many resources.
   */
  public static void printStatistics(
      final Statistics pStatistics, final PrintStream pOut, final LogManager pLogger) {
    final String name = getStatisticsName(pStatistics);
    if (!Strings.isNullOrEmpty(pStatistics.getName())) {
      pOut.println();
      pOut.println(name);
      pOut.println("-".repeat(name.length()));
    }

    final Timer timer = new Timer();
    timer.start();
    try {
      pStatistics.printStatistics(pOut);
    } catch (OutOfMemoryError e) {
      pLogger.logUserException(
          Level.WARNING,
          e,
          "Out of memory while generating statistics from " + name + " and writing output files");
    }
    timer.stop();
    if (timer.getLengthOfLastInterval().compareTo(STATISTICS_WARNING_TIME) > 0) {
      pLogger.logf(Level.WARNING, "Generating statistics from %s took %s.", name, timer);
    }
  }

  private static String getStatisticsName(final Statistics pStatistics) {
    if (Strings.isNullOrEmpty(pStatistics.getName())) {
      return pStatistics.getClass().getName();
    } else {
      return pStatistics.getName() + " statistics";
    }
  }

  public abstract static class AbstractStatValue {

    private final String title;
    private final StatKind mainStatisticKind;

    protected AbstractStatValue(StatKind pMainStatisticKind, String pTitle) {
      title = pTitle;
      mainStatisticKind = pMainStatisticKind;
    }

    public String getTitle() {
      return title;
    }

    /**
     * How many times was this statistical value updated.
     *
     * @return A nonnegative number.
     */
    public abstract int getUpdateCount();

    public StatKind getMainStatisticKind() {
      return mainStatisticKind;
    }
  }

  public enum StatKind {
    SUM,
    COUNT,
    AVG,
    MIN,
    MAX
  }
}
