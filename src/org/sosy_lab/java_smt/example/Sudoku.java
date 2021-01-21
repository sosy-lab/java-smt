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
 * This program parses user-given Sudoku and solves it with an SMT solver.
 *
 * <p>This program is just an example and clearly SMT is not the best solution for solving Sudoku.
 * There might be other algorithms out there that are better suited for solving Sudoku.
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

    // for (Solvers solver : Solvers.values()) {
    {
      Solvers solver = Solvers.MATHSAT5;
      try (SolverContext context =
          SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {
        Integer[][] grid = readGridFromStdin();

        SudokuSolver<?> sudoku = new IntegerBasedSudokuSolver(context);
        // SudokuSolver<?> sudoku2 = new BooleanBasedSudokuSolver(context);
        Integer[][] solution = sudoku.solve(grid);

        if (solution == UNSOLVABLE_SUDOKU) {
          System.out.println("Sudoku has no solution.");
        } else {
          System.out.println("Sudoku has a solution:");
          for (Integer[] line : solution) {
            System.out.println(Joiner.on("").join(line));
          }
        }
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
    Scanner s = new Scanner(System.in, Charset.defaultCharset().name());
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
    final IntegerFormulaManager imgr;

    private SudokuSolver(SolverContext pContext) {
      context = pContext;
      bmgr = context.getFormulaManager().getBooleanFormulaManager();
      imgr = context.getFormulaManager().getIntegerFormulaManager();
    }

    abstract S getSymbols();

    abstract List<BooleanFormula> getRules(S symbols);

    abstract List<BooleanFormula> getAssignments(S symbols, Integer[][] grid);

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

    public IntegerBasedSudokuSolver(SolverContext context) {
      super(context);
    }

    /** prepare symbols: one symbol for each of the 9x9 cells. */
    @Override
    IntegerFormula[][] getSymbols() {
      final IntegerFormula[][] symbols = new IntegerFormula[SIZE][SIZE];
      for (int row = 0; row < SIZE; row++) {
        for (int col = 0; col < SIZE; col++) {
          symbols[row][col] = imgr.makeVariable("x_" + row + "_" + col);
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

    /** convert the user-given values into constraints for the solver. */
    @Override
    List<BooleanFormula> getAssignments(IntegerFormula[][] symbols, Integer[][] grid) {
      final List<BooleanFormula> assignments = new ArrayList<>();
      for (int row = 0; row < SIZE; row++) {
        for (int col = 0; col < SIZE; col++) {
          Integer value = grid[row][col];
          if (value != null) {
            assignments.add(imgr.equal(symbols[row][col], imgr.makeNumber(value)));
          }
        }
      }
      return assignments;
    }

    @Override
    Integer getValue(IntegerFormula[][] symbols, Model model, int row, int col) {
      return model.evaluate(symbols[row][col]).intValue();
    }
  }

  public static class BooleanBasedSudokuSolver extends SudokuSolver<BooleanFormula[][][]> {

    private BooleanBasedSudokuSolver(SolverContext context) {
      super(context);
    }

    /** prepare symbols: one symbol for each of the 9x9 cells. */
    @Override
    BooleanFormula[][][] getSymbols() {
      final BooleanFormula[][][] symbols = new BooleanFormula[SIZE][SIZE][SIZE];
      for (int row = 0; row < SIZE; row++) {
        for (int col = 0; col < SIZE; col++) {
          for (int value = 0; value < SIZE; value++) {
            symbols[row][col][value] = bmgr.makeVariable("x_" + row + "_" + col + "_" + value);
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

    /** convert the user-given values into constraints for the solver. */
    @Override
    List<BooleanFormula> getAssignments(BooleanFormula[][][] symbols, Integer[][] grid) {
      final List<BooleanFormula> assignments = new ArrayList<>();
      for (int row = 0; row < SIZE; row++) {
        for (int col = 0; col < SIZE; col++) {
          Integer value = grid[row][col];
          if (value != null) {
            assignments.add(symbols[row][col][value - 1]); // off-by-one!
          }
        }
      }
      return assignments;
    }

    @Override
    Integer getValue(BooleanFormula[][][] symbols, Model model, int row, int col) {
      for (int value = 0; value < SIZE; value++) {
        if (model.evaluate(symbols[row][col][value]).booleanValue()) {
          return value + 1; // off-by-one!
        }
      }
      return null;
    }
  }
}
