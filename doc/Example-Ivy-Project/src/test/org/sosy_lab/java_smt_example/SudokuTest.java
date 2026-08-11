// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt_example;

import com.google.common.base.Joiner;
import com.google.common.base.Splitter;
import com.google.common.base.StandardSystemProperty;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.Parameter;
import org.junit.jupiter.params.ParameterizedClass;
import org.junit.jupiter.params.provider.MethodSource;
import org.sosy_lab.common.NativeLibraries;
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

import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.logging.Level;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assumptions.assumeTrue;


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
@ParameterizedClass
@MethodSource("getAllSolvers")
public class SudokuTest {

  public static List<Solvers> getAllSolvers() {
    return Arrays.asList(Solvers.values());
  }

  @Parameter(0)
  public Solvers solver;

  private static final String OS =
          StandardSystemProperty.OS_NAME.value().toLowerCase(Locale.getDefault()).replace(" ", "");
  private static final String ARCH =
          StandardSystemProperty.OS_ARCH.value().toLowerCase(Locale.getDefault()).replace(" ", "");

  protected static final boolean IS_WINDOWS = OS.startsWith("windows");
  private static final boolean IS_MAC = OS.startsWith("macos");
  private static final boolean IS_LINUX = OS.startsWith("linux");

  private static final boolean IS_ARCH_ARM64 = ARCH.equals("aarch64");

  private Configuration config;
  private LogManager logger;
  private ShutdownNotifier notifier;

  private SolverContext context;

  private static final String input = """
          2..9.6..1
          ..6.4...9
          ...52.4..
          3.2..7.5.
          ...2..1..
          .9.3..7..
          .87.5.31.
          6.3.1.8..
          4....9...
          """;

  private static final String sudokuSolution = """
          248976531
          536148279
          179523468
          312487956
          764295183
          895361742
          987652314
          623714895
          451839627
          """;

  @BeforeEach
  public void init() throws InvalidConfigurationException {
    config = Configuration.defaultConfiguration();
    logger = BasicLogManager.create(config);
    notifier = ShutdownNotifier.createDummy();
  }

  /*
   * We close our context after we are done with a solver to not waste memory.
   */
  @AfterEach
  public final void closeSolver() {
    if (context != null) {
      context.close();
    }
  }

  private boolean isSufficientVersionOfLibcxx(String library) {
    try {
      NativeLibraries.loadLibrary(library);
    } catch (UnsatisfiedLinkError e) {
      for (String dependency : getRequiredLibcxx(library)) {
        if (e.getMessage().contains("version `" + dependency + "' not found")) {
          return false;
        }
      }
    }
    return true;
  }

  private String[] getRequiredLibcxx(String library) {
    return switch (library) {
      case "z3" -> new String[]{"GLIBC_2.34", "GLIBCXX_3.4.26", "GLIBCXX_3.4.29"};
      case "bitwuzlaj" -> new String[]{"GLIBC_2.33", "GLIBCXX_3.4.26", "GLIBCXX_3.4.29"};
      case "opensmtj" -> new String[]{"GLIBC_2.33", "GLIBCXX_3.4.26", "GLIBCXX_3.4.29"};
      case "mathsat5j" -> new String[]{"GLIBC_2.33", "GLIBC_2.38"};
      case "cvc5jni" -> new String[]{"GLIBC_2.32"};
      case "yices2java" -> new String[]{"GLIBC_2.34"};
      default -> new String[]{};
    };
  }

  private boolean isSupportedOperatingSystemAndArchitecture(Solvers solver) {
    return switch (solver) {
      case SMTINTERPOL, PRINCESS ->
        // Any operating system and any architecture is allowed, Java is sufficient
              true;
      case BOOLECTOR, CVC4 -> IS_LINUX && !IS_ARCH_ARM64;
      case YICES2 -> (IS_LINUX && !IS_ARCH_ARM64 && isSufficientVersionOfLibcxx("yices2java"))
              || (IS_WINDOWS && !IS_ARCH_ARM64);
      case CVC5 -> (IS_LINUX && isSufficientVersionOfLibcxx("cvc5jni")) || IS_WINDOWS || IS_MAC;
      case OPENSMT -> IS_LINUX && isSufficientVersionOfLibcxx("opensmtj");
      case BITWUZLA -> (IS_LINUX && isSufficientVersionOfLibcxx("bitwuzlaj")) || (IS_WINDOWS && !IS_ARCH_ARM64);
      case MATHSAT5 -> (IS_LINUX && isSufficientVersionOfLibcxx("mathsat5j")) || (IS_WINDOWS && !IS_ARCH_ARM64);
      case Z3 -> (IS_LINUX && isSufficientVersionOfLibcxx("z3")) || IS_WINDOWS || IS_MAC;
      case Z3_WITH_INTERPOLATION -> IS_LINUX && !IS_ARCH_ARM64;
    };
  }

  @Test
  public void checkSudoku()
          throws InvalidConfigurationException, InterruptedException, SolverException {
    assumeTrue(isSupportedOperatingSystemAndArchitecture(solver));

    logger.log(Level.INFO, "Executing " + solver + "...");

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
    List<String> lines = Splitter.on('\n').splitToList(puzzle);
    Integer[][] grid = new Integer[lines.size()][lines.size()];

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

