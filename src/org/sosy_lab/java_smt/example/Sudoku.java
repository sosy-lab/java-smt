// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Unlicense OR Apache-2.0 OR MIT

package org.sosy_lab.java_smt.example;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import java.io.IOException;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.List;
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
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * This program parses user-given Sudoku and solves it with an SMT solver.
 *
 * <p>This program is just an example and provides several distinct strategies for encoding the
 * Sudoku problem as SMT. Clearly SMT is not the best solution for solving Sudoku. There might be
 * other algorithms out there that are specialized and better suited for solving Sudoku.
 *
 * <p>Our strategies:
 *
 * <ul>
 *   <li>Integer-based: We encode all values as integer formulas for a range from 1 to 9. Straight
 *       forward, simple to understand, but slow.
 *   <li>Enumeration-based: We encode all values as enumeration formulas for enumeration values from
 *       ONE to NINE. Reasonable fast (up to 10x faster than integer-based strategy).
 *   <li>Boolean-based: We use one more dimension to encode values for the 2D-grid and a
 *       one-hot-encoding. Fastest SMT-based solution, because it is purely based on SAT, and no
 *       additional SMT theory is applied.
 * </ul>
 *
 * <p>The more numbers are available in a Sudoku, the easier it can be solved. A completely empty
 * Sudoku will cause the longest runtime in the solver, because it will guess a lot of values.
 *
 * <p>The Sudoku is read from StdIn and should be formatted as the following example:
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
 * <p>The solution will then be printed on StdOut, just like the following solution:
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
@SuppressWarnings("unused")
public class Sudoku {

  public static final int SIZE = 9;
  private static final int BLOCKSIZE = 3;
  private static final Integer[][] UNSOLVABLE_SUDOKU = null;

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException, IOException {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    Integer[][] grid = readGridFromStdin();
    // for (Solvers solver : Solvers.values()) {
    {
      Solvers solver = Solvers.Z3;
      try (SolverContext context =
          SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {

        for (SudokuSolver<?> sudoku :
            List.of(
                new IntegerBasedSudokuSolver(context),
                new EnumerationBasedSudokuSolver(context),
                new BooleanBasedSudokuSolver(context))) {
          long start = System.currentTimeMillis();

          Integer[][] solution = sudoku.solve(grid);
          if (solution == UNSOLVABLE_SUDOKU) {
            System.out.println("Sudoku has no solution.");
          } else {
            System.out.println("Sudoku has a solution:");
            for (Integer[] line : solution) {
              System.out.println(Joiner.on("").join(line));
            }
          }

          long end = System.currentTimeMillis();
          System.out.println("    Used strategy: " + sudoku.getClass().getSimpleName());
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

  private Sudoku() {}

  /**
   * a simple parser for a half-filled Sudoku.
   *
   * <p>Use digits 0-9 as values, other values will be set to 'unknown'.
   */
  private static Integer[][] readGridFromStdin() {
    Integer[][] grid = new Integer[SIZE][SIZE];
    System.out.println("Insert Sudoku:");
    @SuppressWarnings("resource") // closing Scanner will close StdIn, and we do not want this
    Scanner s = new Scanner(System.in, Charset.defaultCharset());
    for (int row = 0; row < SIZE; row++) {
      String line = s.nextLine().trim();
      for (int col = 0; col < Math.min(line.length(), SIZE); col++) {
        char nextNumber = line.charAt(col);
        if ('0' <= nextNumber && nextNumber <= '9') {
          grid[row][col] = nextNumber - '0';
        }
      }
    }
    return grid;
  }

  public abstract static class SudokuSolver<S> {

    private final SolverContext context;
    final BooleanFormulaManager bmgr;

    private SudokuSolver(SolverContext pContext) {
      context = pContext;
      bmgr = context.getFormulaManager().getBooleanFormulaManager();
    }

    abstract S getSymbols();

    abstract List<BooleanFormula> getRules(S symbols);

    /** convert the user-given values into constraints for the solver. */
    private List<BooleanFormula> getAssignments(S symbols, Integer[][] grid) {
      final List<BooleanFormula> assignments = new ArrayList<>();
      for (int row = 0; row < SIZE; row++) {
        for (int col = 0; col < SIZE; col++) {
          Integer value = grid[row][col];
          if (value != null) {
            assignments.add(getAssignment(symbols, row, col, value));
          }
        }
      }
      return assignments;
    }

    /** convert one user-given value at given coordinate into a constraint for the solver. */
    abstract BooleanFormula getAssignment(S symbols, int row, int col, Integer value);

    abstract Integer getValue(S symbols, Model model, int row, int col);

    /**
     * Solves a sudoku using the given grid values and returns a possible solution. Return <code>
     * Null
     * </code> if Sudoku cannot be solved.
     */
    @Nullable
    public Integer[][] solve(Integer[][] grid) throws InterruptedException, SolverException {
      S symbols = getSymbols();
      List<BooleanFormula> rules = getRules(symbols);
      List<BooleanFormula> assignments = getAssignments(symbols, grid);

      // solve Sudoku
      try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
        prover.push(bmgr.and(rules));
        prover.push(bmgr.and(assignments));

        boolean isUnsolvable = prover.isUnsat(); // the hard part
        if (isUnsolvable) {
          return UNSOLVABLE_SUDOKU;
        }

        // get model and convert it
        Integer[][] solution = new Integer[SIZE][SIZE];
        try (Model model = prover.getModel()) {
          for (int row = 0; row < SIZE; row++) {
            for (int col = 0; col < SIZE; col++) {
              solution[row][col] = getValue(symbols, model, row, col);
            }
          }
        }
        return solution;
      }
    }
  }

  public static class IntegerBasedSudokuSolver extends SudokuSolver<IntegerFormula[][]> {

    final IntegerFormulaManager imgr;

    public IntegerBasedSudokuSolver(SolverContext context) {
      super(context);
      imgr = context.getFormulaManager().getIntegerFormulaManager();
    }

    /** prepare symbols: one symbol for each of the 9x9 cells. */
    @Override
    IntegerFormula[][] getSymbols() {
      final IntegerFormula[][] symbols = new IntegerFormula[SIZE][SIZE];
      for (int row = 0; row < SIZE; row++) {
        for (int col = 0; col < SIZE; col++) {
          symbols[row][col] = imgr.makeVariable("xi_" + row + "_" + col);
        }
      }
      return symbols;
    }

    /**
     * build the default Sudoku constraints:
     * <li>each symbol has a value from 1 to 9.
     * <li>each column, each row, and each 3x3 block contains 9 distinct integer values.
     */
    @Override
    List<BooleanFormula> getRules(IntegerFormula[][] symbols) {
      final List<BooleanFormula> rules = new ArrayList<>();

      // each symbol has a value from 1 to 9
      IntegerFormula one = imgr.makeNumber(1);
      IntegerFormula nine = imgr.makeNumber(9);
      for (int row = 0; row < SIZE; row++) {
        for (int col = 0; col < SIZE; col++) {
          for (int i = 0; i < SIZE; i++) {
            rules.add(imgr.lessOrEquals(one, symbols[row][col]));
            rules.add(imgr.lessOrEquals(symbols[row][col], nine));
          }
        }
      }

      // row constraints: distinct numbers in all rows
      for (int row = 0; row < SIZE; row++) {
        List<IntegerFormula> lst = new ArrayList<>();
        for (int col = 0; col < SIZE; col++) {
          lst.add(symbols[row][col]);
        }
        rules.add(imgr.distinct(lst));
      }

      // column constraints: distinct numbers in all columns
      for (int col = 0; col < SIZE; col++) {
        List<IntegerFormula> lst = new ArrayList<>();
        for (int row = 0; row < SIZE; row++) {
          lst.add(symbols[row][col]);
        }
        rules.add(imgr.distinct(lst));
      }

      // block constraints: distinct numbers in all 3x3 blocks
      for (int rowB = 0; rowB < SIZE; rowB += BLOCKSIZE) {
        for (int colB = 0; colB < SIZE; colB += BLOCKSIZE) {
          List<IntegerFormula> lst = new ArrayList<>();
          for (int row = rowB; row < rowB + BLOCKSIZE; row++) {
            for (int col = colB; col < colB + BLOCKSIZE; col++) {
              lst.add(symbols[row][col]);
            }
          }
          rules.add(imgr.distinct(lst));
        }
      }

      return rules;
    }

    @Override
    BooleanFormula getAssignment(IntegerFormula[][] symbols, int row, int col, Integer value) {
      return imgr.equal(symbols[row][col], imgr.makeNumber(value));
    }

    @Override
    Integer getValue(IntegerFormula[][] symbols, Model model, int row, int col) {
      return model.evaluate(symbols[row][col]).intValue();
    }
  }

  public static class BooleanBasedSudokuSolver extends SudokuSolver<BooleanFormula[][][]> {

    public BooleanBasedSudokuSolver(SolverContext context) {
      super(context);
    }

    /** prepare symbols: one symbol for each of the 9x9 cells. */
    @Override
    BooleanFormula[][][] getSymbols() {
      final BooleanFormula[][][] symbols = new BooleanFormula[SIZE][SIZE][SIZE];
      for (int row = 0; row < SIZE; row++) {
        for (int col = 0; col < SIZE; col++) {
          for (int value = 0; value < SIZE; value++) {
            symbols[row][col][value] = bmgr.makeVariable("xb_" + row + "_" + col + "_" + value);
          }
        }
      }
      return symbols;
    }

    /**
     * build the default Sudoku constraints:
     * <li>each symbol has a value from 1 to 9.
     * <li>each column, each row, and each 3x3 block contains 9 distinct integer values.
     */
    @Override
    List<BooleanFormula> getRules(BooleanFormula[][][] symbols) {
      final List<BooleanFormula> rules = new ArrayList<>();

      // each symbol has a value from 1 to 9
      for (int row = 0; row < SIZE; row++) {
        for (int col = 0; col < SIZE; col++) {
          rules.add(oneHot(ImmutableList.copyOf(symbols[row][col])));
        }
      }

      // row constraints: distinct numbers in all rows
      for (int row = 0; row < SIZE; row++) {
        for (int value = 0; value < SIZE; value++) {
          List<BooleanFormula> lst = new ArrayList<>();
          for (int col = 0; col < SIZE; col++) {
            lst.add(symbols[row][col][value]);
          }
          rules.add(oneHot(lst));
        }
      }

      // column constraints: distinct numbers in all columns
      for (int col = 0; col < SIZE; col++) {
        for (int value = 0; value < SIZE; value++) {
          List<BooleanFormula> lst = new ArrayList<>();
          for (int row = 0; row < SIZE; row++) {
            lst.add(symbols[row][col][value]);
          }
          rules.add(oneHot(lst));
        }
      }

      // block constraints: distinct numbers in all 3x3 blocks
      for (int rowB = 0; rowB < SIZE; rowB += BLOCKSIZE) {
        for (int colB = 0; colB < SIZE; colB += BLOCKSIZE) {
          for (int value = 0; value < SIZE; value++) {
            List<BooleanFormula> lst = new ArrayList<>();
            for (int row = rowB; row < rowB + BLOCKSIZE; row++) {
              for (int col = colB; col < colB + BLOCKSIZE; col++) {
                lst.add(symbols[row][col][value]);
              }
            }
            rules.add(oneHot(lst));
          }
        }
      }

      return rules;
    }

    /** exactly one of the variables must be true, the rest must be false. */
    private BooleanFormula oneHot(List<BooleanFormula> vars) {
      List<BooleanFormula> oneHot = new ArrayList<>();
      for (int i = 0; i < SIZE; i++) {
        for (int j = 0; j < i; j++) {
          oneHot.add(bmgr.not(bmgr.and(vars.get(i), vars.get(j))));
        }
      }
      oneHot.add(bmgr.or(vars));
      return bmgr.and(oneHot);
    }

    @Override
    BooleanFormula getAssignment(BooleanFormula[][][] symbols, int row, int col, Integer value) {
      return symbols[row][col][value - 1]; // off-by-one!
    }

    @Override
    Integer getValue(BooleanFormula[][][] symbols, Model model, int row, int col) {
      for (int value = 0; value < SIZE; value++) {
        if (model.evaluate(symbols[row][col][value])) {
          return value + 1; // off-by-one!
        }
      }
      return null;
    }
  }

  public static class EnumerationBasedSudokuSolver extends SudokuSolver<EnumerationFormula[][]> {

    private final EnumerationFormulaManager emgr;
    private final EnumerationFormulaType type;
    private static final String[] VALUES = {
      "ONE", "TWO", "THREE", "FOUR", "FIVE", "SIX", "SEVEN", "EIGHT", "NINE",
    };

    public EnumerationBasedSudokuSolver(SolverContext context) {
      super(context);
      emgr = context.getFormulaManager().getEnumerationFormulaManager();
      type = emgr.declareEnumeration("VALUES", VALUES);
    }

    /** prepare symbols: one symbol for each of the 9x9 cells. */
    @Override
    EnumerationFormula[][] getSymbols() {
      final EnumerationFormula[][] symbols = new EnumerationFormula[SIZE][SIZE];
      for (int row = 0; row < SIZE; row++) {
        for (int col = 0; col < SIZE; col++) {
          symbols[row][col] = emgr.makeVariable("xe_" + row + "_" + col, type);
        }
      }
      return symbols;
    }

    /**
     * build the default Sudoku constraints:
     * <li>each symbol has a value from 1 to 9.
     * <li>each column, each row, and each 3x3 block contains 9 distinct integer values.
     */
    @Override
    List<BooleanFormula> getRules(EnumerationFormula[][] symbols) {
      final List<BooleanFormula> rules = new ArrayList<>();

      // each symbol has a value from 1 to 9
      // -> solved implicitly by using enum-type

      // row constraints: distinct numbers in all rows
      for (int row = 0; row < SIZE; row++) {
        List<EnumerationFormula> lst = new ArrayList<>();
        for (int col = 0; col < SIZE; col++) {
          lst.add(symbols[row][col]);
        }
        rules.add(distinct(lst));
      }

      // column constraints: distinct numbers in all columns
      for (int col = 0; col < SIZE; col++) {
        List<EnumerationFormula> lst = new ArrayList<>();
        for (int row = 0; row < SIZE; row++) {
          lst.add(symbols[row][col]);
        }
        rules.add(distinct(lst));
      }

      // block constraints: distinct numbers in all 3x3 blocks
      for (int rowB = 0; rowB < SIZE; rowB += BLOCKSIZE) {
        for (int colB = 0; colB < SIZE; colB += BLOCKSIZE) {
          List<EnumerationFormula> lst = new ArrayList<>();
          for (int row = rowB; row < rowB + BLOCKSIZE; row++) {
            for (int col = colB; col < colB + BLOCKSIZE; col++) {
              lst.add(symbols[row][col]);
            }
          }
          rules.add(distinct(lst));
        }
      }

      return rules;
    }

    private BooleanFormula distinct(List<EnumerationFormula> lst) {
      if (lst.size() <= 1) {
        return bmgr.makeTrue();
      } else {
        List<BooleanFormula> pairings = new ArrayList<>();
        for (int i = 0; i < lst.size(); i++) {
          for (int j = 0; j < i; j++) {
            pairings.add(bmgr.not(emgr.equivalence(lst.get(i), lst.get(j))));
          }
        }
        return bmgr.and(pairings);
      }
    }

    @Override
    BooleanFormula getAssignment(EnumerationFormula[][] symbols, int row, int col, Integer value) {
      // index-shift required
      return emgr.equivalence(symbols[row][col], emgr.makeConstant(VALUES[value - 1], type));
    }

    @Override
    Integer getValue(EnumerationFormula[][] symbols, Model model, int row, int col) {
      String value = model.evaluate(symbols[row][col]);
      for (int i = 0; i < VALUES.length; i++) {
        if (VALUES[i].equals(value)) {
          return i + 1; // index-shift required
        }
      }
      return null;
    }
  }
}
