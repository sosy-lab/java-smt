package com.mycompany.app;

import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertEquals;

import org.junit.Test;
import org.junit.After;
import org.junit.Before;
import com.google.common.base.Joiner;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Arrays;
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
   * This program parses a String-given Sudoku and solves it with an SMT solver.
   *
   * <p>
   * This program is just an example and clearly SMT is not the best solution for solving Sudoku.
   * There might be other algorithms out there that are better suited for solving Sudoku.
   *
   * <p>
   * The more numbers are available in a Sudoku, the easier it can be solved. A completely empty
   * Sudoku will cause the longest runtime in the solver, because it will guess a lot of values.
   *
   * <p>
   * The Sudoku is read from a String and should be formatted as the following example:
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
   * <p>
   * The solution will then be printed on StdOut and checked by an assertion, just like the following solution:
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
  public class SudokuTest {
    
    private Configuration config;
    private LogManager logger;
    private ShutdownNotifier notifier;
    
    private SolverContext context;

    private static final int SIZE = 9;
    private static final int BLOCKSIZE = 3;
    private static final Integer[][] UNSOLVABLE_SUDOKU = new Integer[0][0];

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
          "248976531\n" +
          "536148279\n" +
          "179523468\n" +
          "312487956\n" +
          "764295183\n" +
          "895361742\n" +
          "987652314\n" +
          "623714895\n" +
          "451839627\n";
    
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
    public void princessSudokuTest() throws InvalidConfigurationException, InterruptedException, SolverException {
      Solvers solver = Solvers.PRINCESS;
      context = SolverContextFactory.createSolverContext(config, logger, notifier, solver);
      Integer[][] grid = readGridFromString(input);

      SudokuSolver<?> sudoku = new IntegerBasedSudokuSolver(context);
      Integer[][] solution = sudoku.solve(grid);

      assertNotEquals(solution, UNSOLVABLE_SUDOKU);
      assertEquals(sudokuSolution, solutionToString(solution));
    }
    
    @Test
    public void z3SudokuTest() throws InvalidConfigurationException, InterruptedException, SolverException {
      Solvers solver = Solvers.Z3;

        context = SolverContextFactory.createSolverContext(config, logger, notifier, solver);
        Integer[][] grid = readGridFromString(input);

        SudokuSolver<?> sudoku = new IntegerBasedSudokuSolver(context);
        Integer[][] solution = sudoku.solve(grid);

        assertNotEquals(solution, UNSOLVABLE_SUDOKU);
        assertEquals(sudokuSolution, solutionToString(solution));

    }
    

    @Test
    public void mathsatSudokuTest() throws InvalidConfigurationException, InterruptedException, SolverException {
      Solvers solver = Solvers.MATHSAT5;

        context = SolverContextFactory.createSolverContext(config, logger, notifier, solver);
        Integer[][] grid = readGridFromString(input);

        SudokuSolver<?> sudoku = new IntegerBasedSudokuSolver(context);
        Integer[][] solution = sudoku.solve(grid);

        assertNotEquals(solution, UNSOLVABLE_SUDOKU);
        assertEquals(sudokuSolution, solutionToString(solution));
    }
    
    private String solutionToString(Integer[][] solution) {
      StringBuilder sb = new StringBuilder();
        for(Integer[] s1 : solution){
          for(Integer i : s1) {
            sb.append(i);
          }
          sb.append('\n');
        }
      return sb.toString();
    }

    /**
     * a simple parser for a half-filled Sudoku.
     *
     * <p>
     * Use digits 0-9 as values, other values will be set to 'unknown'.
     */
    private Integer[][] readGridFromString(String puzzle) {
      Integer[][] grid = new Integer[SIZE][SIZE];
      String[] lines = puzzle.split("\n");

      for (int row = 0; row < lines.length; row++) {
        for (int col = 0; col < lines[row].length(); col++) {
          char nextNumber = lines[row].charAt(col);
          if ('0' <= nextNumber && nextNumber <= '9') {
            grid[row][col] = nextNumber - '0';
          }
        }
      }
      return grid;
    }

    private abstract class SudokuSolver<S> {

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
      private Integer[][] solve(Integer[][] grid) throws InterruptedException, SolverException {
        S symbols = getSymbols();
        List<BooleanFormula> rules = getRules(symbols);
        List<BooleanFormula> assignments = getAssignments(symbols, grid);

        // solve Sudoku
        try (ProverEnvironment prover =
            context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
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

    private class IntegerBasedSudokuSolver extends SudokuSolver<IntegerFormula[][]> {

      private IntegerBasedSudokuSolver(SolverContext context) {
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
  }

