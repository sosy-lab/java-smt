// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt_example;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assume.assumeTrue;
import static org.sosy_lab.java_smt.example.Sudoku.SIZE;

import com.google.common.base.Joiner;
import com.google.common.base.Splitter;
import java.util.Arrays;
import java.util.List;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.example.Sudoku;
import org.sosy_lab.java_smt.example.Sudoku.SudokuSolver;

/**
 * This program parses a String-given Sudoku and solves it with an SMT solver.
 *
 * <p>This program is just an example and clearly SMT is not the best solution for solving Sudoku.
 * There might be other algorithms out there that are better suited for solving Sudoku.
 *
 * <p>The more numbers are available in a Sudoku, the easier it can be solved. A completely empty
 * Sudoku will cause the longest runtime in the solver, because it will guess a lot of values.
 *
 * <p>The Sudoku is read from a String and should be formatted as the following example:
 *
 * <pre>
 * 2..9.6..1
 * ..6.4...9
 * ...52.4..
 * 3.2..7.5.
 * ...2..1..
 * .9.3..7..
 * .87.5.31.
 * 6.3.1.8..
 * 4....9...
 * </pre>
 *
 * <p>The solution will then be printed on StdOut and checked by an assertion, just like the
 * following solution:
 *
 * <pre>
 * 248976531
 * 536148279
 * 179523468
 * 312487956
 * 764295183
 * 895361742
 * 987652314
 * 623714895
 * 451839627
 * </pre>
 */
@RunWith(Parameterized.class)
public class SudokuTest {

  @Parameterized.Parameters(name = "{0}")
  public static List<Solvers> getSolvers() {
    return Arrays.asList(Solvers.values());
  }

  @Parameterized.Parameter(0)
  public Solvers solver;

  private static final String OS = System.getProperty("os.name").toLowerCase().replace(" ", "");
  private static final boolean IS_WINDOWS = OS.startsWith("windows");
  private static final boolean IS_MAC = OS.startsWith("macos");
  private static final boolean IS_LINUX = OS.startsWith("linux");

  /**
   * Let's allow to disable some checks on certain combinations of operating systems and solvers,
   * because of missing support.
   *
   * <p>We update this list, whenever a new solver or operating system is added.
   */
  private static boolean isOperatingSystemSupported(Solvers solver) {
    switch (solver) {
      case SMTINTERPOL:
      case PRINCESS:
        // any operating system is allowed, Java is already available.
        return true;
      case BOOLECTOR:
      case CVC4:
      case CVC5:
      case OPENSMT:
      case YICES2:
        return IS_LINUX;
      case MATHSAT5:
      case BITWUZLA:
        return IS_LINUX || IS_WINDOWS;
      case Z3:
        return IS_LINUX || IS_WINDOWS || IS_MAC;
      default:
        throw new AssertionError("unexpected solver: " + solver);
    }
  }

  private Configuration config;
  private LogManager logger;
  private ShutdownNotifier notifier;

  private SolverContext context;

  private static final String input =
      "2..9.6..1\n"
          + "..6.4...9\n"
          + "...52.4..\n"
          + "3.2..7.5.\n"
          + "...2..1..\n"
          + ".9.3..7..\n"
          + ".87.5.31.\n"
          + "6.3.1.8..\n"
          + "4....9...";

  private static final String sudokuSolution =
      "248976531\n"
          + "536148279\n"
          + "179523468\n"
          + "312487956\n"
          + "764295183\n"
          + "895361742\n"
          + "987652314\n"
          + "623714895\n"
          + "451839627\n";

  @Before
  public void init() throws InvalidConfigurationException {
    config = Configuration.defaultConfiguration();
    logger = BasicLogManager.create(config);
    notifier = ShutdownNotifier.createDummy();
  }

  /*
   * We close our context after we are done with a solver to not waste memory.
   */
  @After
  public final void closeSolver() {
    if (context != null) {
      context.close();
    }
  }

  @Test
  public void checkSudoku()
      throws InvalidConfigurationException, InterruptedException, SolverException {
    assumeTrue(isOperatingSystemSupported(solver));

    context = SolverContextFactory.createSolverContext(config, logger, notifier, solver);
    Integer[][] grid = readGridFromString(input);

    SudokuSolver<?> sudoku = new Sudoku.BooleanBasedSudokuSolver(context);
    Integer[][] solution = sudoku.solve(grid);

    assertNotNull(solution);
    assertEquals(sudokuSolution, solutionToString(solution));
  }

  private String solutionToString(Integer[][] solution) {
    StringBuilder sb = new StringBuilder();
    for (Integer[] s1 : solution) {
      sb.append(Joiner.on("").join(s1)).append('\n');
    }
    return sb.toString();
  }

  /**
   * a simple parser for a half-filled Sudoku.
   *
   * <p>Use digits 0-9 as values, other values will be set to 'unknown'.
   */
  private Integer[][] readGridFromString(String puzzle) {
    Integer[][] grid = new Integer[SIZE][SIZE];
    List<String> lines = Splitter.on('\n').splitToList(puzzle);

    for (int row = 0; row < lines.size(); row++) {
      for (int col = 0; col < lines.get(row).length(); col++) {
        char nextNumber = lines.get(row).charAt(col);
        if ('0' <= nextNumber && nextNumber <= '9') {
          grid[row][col] = nextNumber - '0';
        }
      }
    }
    return grid;
  }
}
