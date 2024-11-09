// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Unlicense OR Apache-2.0 OR MIT

package org.sosy_lab.java_smt.example;

import com.google.common.base.Preconditions;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Scanner;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * This program parses a user-given Binoxxo and solves it with an SMT solver. Binoxxo is a
 * grid-based Sudoku-like puzzle with values 'O' and 'X' and follows the following rules:
 *
 * <ul>
 *   <li>In each column or row there are as many 'X's as 'O's.
 *   <li>Three aligned cells must not contains an identical value.
 * </ul>
 *
 * <p>The Binoxxo is read from StdIn and should be formatted as the following example:
 *
 * <pre>
 * X..O...XX.
 * .O.O....X.
 * OO..O..X..
 * ...O....X.
 * .O........
 * .O.....O.X
 * X...X.O...
 * .X..XO...X
 * X.....OO..
 * X..X..O..O
 * </pre>
 *
 * <p>A empty newline will terminate the input and start the solving process.
 *
 * <p>The solution will then be printed on StdOut, just like the following solution:
 *
 * <pre>
 * XXOOXOOXXO
 * OOXOOXXOXX
 * OOXXOOXXOX
 * XXOOXXOOXO
 * OOXXOOXXOX
 * OOXXOXXOOX
 * XXOOXXOOXO
 * OXOOXOXXOX
 * XOXXOXOOXO
 * XXOXXOOXOO
 * </pre>
 */
@SuppressWarnings("unused")
public final class Binoxxo {

  private static final char[][] UNSOLVABLE_BINOXXO = null;

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException, IOException {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    char[][] grid = readGridFromStdin();
    // for (Solvers solver : Solvers.values()) {
    {
      Solvers solver = Solvers.Z3;
      try (SolverContext context =
          SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {

        for (BinoxxoSolver<?> binoxxo :
            List.of(
                new IntegerBasedBinoxxoSolver(context), new BooleanBasedBinoxxoSolver(context))) {
          long start = System.currentTimeMillis();

          char[][] solution = binoxxo.solve(grid);
          if (solution == UNSOLVABLE_BINOXXO) {
            System.out.println("Binoxxo has no solution.");
          } else {
            System.out.println("Binoxxo has a solution:");
            for (char[] line : solution) {
              System.out.println(line);
            }
          }

          long end = System.currentTimeMillis();
          System.out.println("    Used strategy: " + binoxxo.getClass().getSimpleName());
          System.out.println("    Time to solve: " + (end - start) + " ms");
        }
      } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

        // on some machines we support only some solvers,
        // thus we can ignore these errors.
        logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");

      } catch (UnsupportedOperationException e) {
        logger.logUserException(Level.INFO, e, e.getMessage());
      }
    }
  }

  private Binoxxo() {}

  /**
   * a simple parser for a half-filled Binoxxo.
   *
   * <p>Use 'X' and 'O' as values, other values will be set to 'unknown'.
   */
  private static char[][] readGridFromStdin() {
    @SuppressWarnings("resource") // closing Scanner will close StdIn, and we do not want this
    Scanner scanner = new Scanner(System.in, Charset.defaultCharset());
    System.out.println(
        "Please insert a square for Binxxo.\n"
            + "Use 'X', 'O' as values any any other char as missing value.\n"
            + "Use an empty line to terminate your input.");

    // read all input
    String line = scanner.nextLine();
    List<String> lines = new ArrayList<>();
    while (!line.isEmpty()) {
      lines.add(line.toUpperCase(Locale.getDefault()));
      line = scanner.nextLine();
    }

    // convert input to grid
    int size = lines.size();
    Preconditions.checkArgument(size % 2 == 0, "Invalid Binoxxo: size is not divisibl by 2");
    char[][] grid = new char[size][size];
    for (int i = 0; i < size; i++) {
      Preconditions.checkArgument(lines.get(i).length() == size, "Invalid Binoxxo: no square");
      for (int j = 0; j < size; j++) {
        char value = lines.get(i).charAt(j);
        grid[i][j] = (value == 'X' || value == 'O') ? value : '.'; // normalize unwanted input
      }
    }
    return grid;
  }

  public abstract static class BinoxxoSolver<S> {

    private final SolverContext context;
    final BooleanFormulaManager bmgr;

    private BinoxxoSolver(SolverContext pContext) {
      context = pContext;
      bmgr = context.getFormulaManager().getBooleanFormulaManager();
    }

    abstract S getSymbols(char[][] grid);

    abstract List<BooleanFormula> getRules(S symbols);

    /** convert the user-given values into constraints for the solver. */
    private List<BooleanFormula> getAssignments(S symbols, char[][] grid) {
      final List<BooleanFormula> assignments = new ArrayList<>();
      for (int row = 0; row < grid.length; row++) {
        for (int col = 0; col < grid[row].length; col++) {
          char value = grid[row][col];
          if (value != '.') {
            assignments.add(getAssignment(symbols, row, col, value));
          }
        }
      }
      return assignments;
    }

    /** convert one user-given value at given coordinate into a constraint for the solver. */
    abstract BooleanFormula getAssignment(S symbols, int row, int col, char value);

    abstract char getValue(S symbols, Model model, int row, int col) throws InterruptedException;

    /**
     * Solves a Binoxxo using the given grid values and returns a possible solution. Return <code>
     * Null
     * </code> if Binoxxo cannot be solved.
     */
    public char[][] solve(char[][] grid) throws InterruptedException, SolverException {
      S symbols = getSymbols(grid);
      List<BooleanFormula> rules = getRules(symbols);
      List<BooleanFormula> assignments = getAssignments(symbols, grid);

      // solve Binoxxo
      try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
        prover.push(bmgr.and(rules));
        prover.push(bmgr.and(assignments));

        boolean isUnsolvable = prover.isUnsat(); // the hard part
        if (isUnsolvable) {
          return UNSOLVABLE_BINOXXO;
        }

        // get model and convert it
        char[][] solution = new char[grid.length][];
        try (Model model = prover.getModel()) {
          for (int row = 0; row < grid.length; row++) {
            solution[row] = new char[grid[row].length];
            for (int col = 0; col < grid[row].length; col++) {
              solution[row][col] = getValue(symbols, model, row, col);
            }
          }
        }
        return solution;
      }
    }
  }

  public static class IntegerBasedBinoxxoSolver extends BinoxxoSolver<IntegerFormula[][]> {

    final IntegerFormulaManager imgr;

    public IntegerBasedBinoxxoSolver(SolverContext context) {
      super(context);
      imgr = context.getFormulaManager().getIntegerFormulaManager();
    }

    /** prepare symbols: one symbol for each of the cells. */
    @Override
    IntegerFormula[][] getSymbols(char[][] grid) {
      final IntegerFormula[][] symbols = new IntegerFormula[grid.length][];
      for (int row = 0; row < grid.length; row++) {
        symbols[row] = new IntegerFormula[grid[row].length];
        for (int col = 0; col < grid[row].length; col++) {
          symbols[row][col] = imgr.makeVariable("x_" + row + "_" + col);
        }
      }
      return symbols;
    }

    /**
     * build the default Binoxxo constraints:
     * <li>each cell has value 'X'=1 or 'O'=0.
     * <li>each row and columns has the same number of 'X's and 'O's.
     * <li>three aligned cells must not have the same value.
     */
    @Override
    List<BooleanFormula> getRules(IntegerFormula[][] symbols) {
      final List<BooleanFormula> rules = new ArrayList<>();

      final int size = symbols.length;
      Preconditions.checkArgument(size % 2 == 0);
      final IntegerFormula halfSize = imgr.makeNumber(size / 2);
      final IntegerFormula zero = imgr.makeNumber(0);
      final IntegerFormula one = imgr.makeNumber(1);
      final IntegerFormula two = imgr.makeNumber(2);

      // each cell has value 'X'=1 or 'O'=0.
      for (int row = 0; row < size; row++) {
        for (int col = 0; col < size; col++) {
          rules.add(
              bmgr.or(imgr.equal(zero, symbols[row][col]), imgr.equal(one, symbols[row][col])));
        }
      }

      // row constraints: each row and columns has the same number of 'X's and 'O's
      for (int row = 0; row < size; row++) {
        List<IntegerFormula> lst = new ArrayList<>();
        for (int col = 0; col < size; col++) {
          lst.add(symbols[row][col]);
        }
        rules.add(imgr.equal(imgr.sum(lst), halfSize));
      }

      // column constraints: each row and columns has the same number of 'X's and 'O's
      for (int col = 0; col < size; col++) {
        List<IntegerFormula> lst = new ArrayList<>();
        for (int row = 0; row < size; row++) {
          lst.add(symbols[row][col]);
        }
        rules.add(imgr.equal(imgr.sum(lst), halfSize));
      }

      // neighbor constraints: each 3x1 block contains at least 2 identical values
      for (int row = 0; row < size; row++) {
        for (int col = 0; col < size - 2; col++) {
          List<IntegerFormula> lst =
              List.of(symbols[row][col], symbols[row][col + 1], symbols[row][col + 2]);
          IntegerFormula sum = imgr.sum(lst);
          rules.add(bmgr.or(imgr.equal(one, sum), imgr.equal(two, sum)));
        }
      }

      // neighbor constraints: each 1x3 block contains at least 2 identical values
      for (int col = 0; col < size; col++) {
        for (int row = 0; row < size - 2; row++) {
          List<IntegerFormula> lst =
              List.of(symbols[row][col], symbols[row + 1][col], symbols[row + 2][col]);
          IntegerFormula sum = imgr.sum(lst);
          rules.add(bmgr.or(imgr.equal(one, sum), imgr.equal(two, sum)));
        }
      }

      return rules;
    }

    @Override
    BooleanFormula getAssignment(IntegerFormula[][] symbols, int row, int col, char value) {
      return imgr.equal(symbols[row][col], imgr.makeNumber(value == 'O' ? 0 : 1));
    }

    @Override
    char getValue(IntegerFormula[][] symbols, Model model, int row, int col)
        throws InterruptedException {
      @Nullable BigInteger value = model.evaluate(symbols[row][col]);
      return value == null ? '.' : value.intValue() == 0 ? 'O' : 'X';
    }
  }

  /**
   * This solver encodes nore steps into boolean logic, which makes it about 10x faster than the
   * {@link IntegerBasedBinoxxoSolver}.
   */
  public static class BooleanBasedBinoxxoSolver extends BinoxxoSolver<BooleanFormula[][]> {

    final IntegerFormulaManager imgr;

    public BooleanBasedBinoxxoSolver(SolverContext context) {
      super(context);
      imgr = context.getFormulaManager().getIntegerFormulaManager();
    }

    /** prepare symbols: one symbol for each of the cells. */
    @Override
    BooleanFormula[][] getSymbols(char[][] grid) {
      final BooleanFormula[][] symbols = new BooleanFormula[grid.length][];
      for (int row = 0; row < grid.length; row++) {
        symbols[row] = new BooleanFormula[grid[row].length];
        for (int col = 0; col < grid[row].length; col++) {
          symbols[row][col] = bmgr.makeVariable("x_" + row + "_" + col);
        }
      }
      return symbols;
    }

    /**
     * build the default Binoxxo constraints:
     * <li>each cell has value 'X'=1 or 'O'=0.
     * <li>each row and columns has the same number of 'X's and 'O's.
     * <li>three aligned cells must not have the same value.
     */
    @Override
    List<BooleanFormula> getRules(BooleanFormula[][] symbols) {
      final List<BooleanFormula> rules = new ArrayList<>();

      final int size = symbols.length;
      Preconditions.checkArgument(size % 2 == 0);
      final IntegerFormula halfSize = imgr.makeNumber(size / 2);
      final IntegerFormula zero = imgr.makeNumber(0);
      final IntegerFormula one = imgr.makeNumber(1);

      // TODO replace the next lines with a real boolean bit-counter instead of relying on Integers
      // row constraints: each row and columns has the same number of 'X's and 'O's
      for (int row = 0; row < size; row++) {
        List<IntegerFormula> lst = new ArrayList<>();
        for (int col = 0; col < size; col++) {
          lst.add(bmgr.ifThenElse(symbols[row][col], one, zero));
        }
        rules.add(imgr.equal(imgr.sum(lst), halfSize));
      }

      // TODO replace the next lines with a real boolean bit-counter instead of relying on Integers
      // column constraints: each row and columns has the same number of 'X's and 'O's
      for (int col = 0; col < size; col++) {
        List<IntegerFormula> lst = new ArrayList<>();
        for (int row = 0; row < size; row++) {
          lst.add(bmgr.ifThenElse(symbols[row][col], one, zero));
        }
        rules.add(imgr.equal(imgr.sum(lst), halfSize));
      }

      // neighbor constraints: each 3x1 block contains at least 2 identical values
      for (int row = 0; row < size; row++) {
        for (int col = 0; col < size - 2; col++) {
          List<BooleanFormula> lst =
              List.of(symbols[row][col], symbols[row][col + 1], symbols[row][col + 2]);
          rules.add(bmgr.not(bmgr.and(lst)));
          rules.add(bmgr.or(lst));
        }
      }

      // neighbor constraints: each 1x3 block contains at least 2 identical values
      for (int col = 0; col < size; col++) {
        for (int row = 0; row < size - 2; row++) {
          List<BooleanFormula> lst =
              List.of(symbols[row][col], symbols[row + 1][col], symbols[row + 2][col]);
          rules.add(bmgr.not(bmgr.and(lst)));
          rules.add(bmgr.or(lst));
        }
      }

      return rules;
    }

    @Override
    BooleanFormula getAssignment(BooleanFormula[][] symbols, int row, int col, char value) {
      return value == 'O' ? bmgr.not(symbols[row][col]) : symbols[row][col];
    }

    @Override
    char getValue(BooleanFormula[][] symbols, Model model, int row, int col)
        throws InterruptedException {
      @Nullable Boolean value = model.evaluate(symbols[row][col]);
      return value == null ? '.' : value ? 'X' : 'O';
    }
  }
}
