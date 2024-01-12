// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Unlicense OR Apache-2.0 OR MIT

package org.sosy_lab.java_smt.example.nqueens_user_propagator;

import com.google.common.base.Verify;
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * This example program solves a NQueens problem of given size and prints a possible solution.
 *
 * <p>For example, the Queen can be placed in these ways for a field size of 4:
 *
 * <pre>
 *   .Q..
 *   ...Q
 *   Q...
 *   ..Q.
 * </pre>
 */
public class NQueens {
  private final SolverContext context;
  private final BooleanFormulaManager bmgr;
  private final int n;
  private NQueensEnumeratingPropagator theorySolver;

  public NQueens(SolverContext pContext, int n) {
    context = pContext;
    bmgr = context.getFormulaManager().getBooleanFormulaManager();
    this.n = n;
  }

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    try (SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, notifier, Solvers.Z3);
         ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS,
             ProverOptions.GENERATE_ALL_SAT)) {
      int n = Integer.parseInt(args[0]);
      int method = Integer.parseInt(args[1]);

      long timeSnapshot = System.currentTimeMillis();
      NQueens myQueen = new NQueens(context, n);
      int solutions;
      if (method == 1) {
        System.out.println("Enumerating Nqueens solutions with classical blocking clauses.");
        solutions = myQueen.enumerateSolutionsClassic(prover);
      } else if (method == 2) {
        System.out.println("Enumerating Nqueens solutions with enumerating propagator.");
        solutions = myQueen.enumerateSolutionsWithPropagator(prover);
      } else if (method == 3) {
        System.out.println("Enumerating Nqueens solutions with enumerating and constraining propagator.");
        solutions = myQueen.enumerateSolutionsWithConstraintPropagator(prover);
      } else {
        throw new IllegalArgumentException("The second method argument must be in {1, 2, 3}.");
      }
      long passedMillis = System.currentTimeMillis() - timeSnapshot;
      System.out.printf("Found %d solutions in %.2f seconds%n", solutions, (passedMillis / 1000d));

    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {
      logger.logUserException(Level.INFO, e, "Solver Z3 is not available.");
    } catch (UnsupportedOperationException e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }
  }


  /**
   * Creates a 2D array of BooleanFormula objects to represent the variables for each cell in a grid
   * of size N x N.
   *
   * @return a 2D array of BooleanFormula objects, where each BooleanFormula object represents a
   *     variable for a cell in the grid.
   */
  private BooleanFormula[][] getSymbols() {
    final BooleanFormula[][] symbols = new BooleanFormula[n][n];
    for (int row = 0; row < n; row++) {
      for (int col = 0; col < n; col++) {
        symbols[row][col] = bmgr.makeVariable("q_" + row + "_" + col);
      }
    }
    return symbols;
  }

  /**
   * Rule 1: At least one queen per row, or we can say make sure that there are N Queens on the
   * board.
   *
   * @param symbols a 2D Boolean array representing the board. Each element is true if there is a
   *     queen in that cell, false otherwise.
   * @return a List of BooleanFormulas representing the rules for this constraint.
   */
  private List<BooleanFormula> rowRule1(BooleanFormula[][] symbols) {
    final List<BooleanFormula> rules = new ArrayList<>();
    for (BooleanFormula[] rowSymbols : symbols) {
      List<BooleanFormula> clause = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        clause.add(rowSymbols[i]);
      }
      rules.add(bmgr.or(clause));
    }
    return rules;
  }

  /**
   * Rule 2: Add constraints to ensure that at most one queen is placed in each row. For n=4:
   *
   * <pre>
   *   0123
   * 0 ----
   * 1 ----
   * 2 ----
   * 3 ----
   * </pre>
   *
   * <p>We add a negation of the conjunction of all possible pairs of variables in each row.
   *
   * @param symbols a 2D array of BooleanFormula objects representing the variables for each cell on
   *     the board.
   * @return a list of BooleanFormula objects representing the constraints added by this rule.
   */
  private List<BooleanFormula> rowRule2(BooleanFormula[][] symbols) {
    final List<BooleanFormula> rules = new ArrayList<>();
    for (BooleanFormula[] rowSymbol : symbols) {
      for (int j1 = 0; j1 < n; j1++) {
        for (int j2 = j1 + 1; j2 < n; j2++) {
          rules.add(bmgr.not(bmgr.and(rowSymbol[j1], rowSymbol[j2])));
        }
      }
    }
    return rules;
  }

  /**
   * Rule 3: Add constraints to ensure that at most one queen is placed in each column. For n=4:
   *
   * <pre>
   *   0123
   * 0 ||||
   * 1 ||||
   * 2 ||||
   * 3 ||||
   * </pre>
   *
   * <p>We add a negation of the conjunction of all possible pairs of variables in each column.
   *
   * @param symbols a 2D array of BooleanFormula representing the placement of queens on the
   *     chessboard
   * @return a list of BooleanFormula objects representing the constraints added by this rule.
   */
  private List<BooleanFormula> columnRule(BooleanFormula[][] symbols) {
    final List<BooleanFormula> rules = new ArrayList<>();
    for (int j = 0; j < n; j++) {
      for (int i1 = 0; i1 < n; i1++) {
        for (int i2 = i1 + 1; i2 < n; i2++) {
          rules.add(bmgr.not(bmgr.and(symbols[i1][j], symbols[i2][j])));
        }
      }
    }
    return rules;
  }

  /**
   * Rule 4: At most one queen per diagonal transform the field (=symbols) from square shape into a
   * (downwards/upwards directed) rhombus that is embedded in a rectangle
   * (=downwardDiagonal/upwardDiagonal). For example for N=4 from this square:
   *
   * <pre>
   *   0123
   * 0 xxxx
   * 1 xxxx
   * 2 xxxx
   * 3 xxxx
   * </pre>
   *
   * <p>to this rhombus/rectangle:
   *
   * <pre>
   *   0123
   * 0 x---
   * 1 xx--
   * 2 xxx-
   * 3 xxxx
   * 4 -xxx
   * 5 --xx
   * 6 ---x
   * </pre>
   *
   * @param symbols a two-dimensional array of Boolean formulas representing the chessboard
   *     configuration
   * @return a list of BooleanFormula objects representing the constraints added by this rule.
   */
  private List<BooleanFormula> diagonalRule(BooleanFormula[][] symbols) {
    final List<BooleanFormula> rules = new ArrayList<>();
    int numDiagonals = 2 * n - 1;
    BooleanFormula[][] downwardDiagonal = new BooleanFormula[numDiagonals][n];
    BooleanFormula[][] upwardDiagonal = new BooleanFormula[numDiagonals][n];
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        downwardDiagonal[i + j][i] = symbols[i][j];
        upwardDiagonal[i - j + n - 1][i] = symbols[i][j];
      }
    }
    for (int d = 0; d < numDiagonals; d++) {
      BooleanFormula[] diagonal1 = downwardDiagonal[d];
      BooleanFormula[] diagonal2 = upwardDiagonal[d];
      List<BooleanFormula> downwardDiagonalQueen = new ArrayList<>();
      List<BooleanFormula> upwardDiagonalQueen = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        if (diagonal1[i] != null) {
          downwardDiagonalQueen.add(diagonal1[i]);
        }
        if (diagonal2[i] != null) {
          upwardDiagonalQueen.add(diagonal2[i]);
        }
      }
      for (int i = 0; i < downwardDiagonalQueen.size(); i++) {
        for (int j = i + 1; j < downwardDiagonalQueen.size(); j++) {
          rules.add(bmgr.not(bmgr.and(downwardDiagonalQueen.get(i), downwardDiagonalQueen.get(j))));
        }
      }
      for (int i = 0; i < upwardDiagonalQueen.size(); i++) {
        for (int j = i + 1; j < upwardDiagonalQueen.size(); j++) {
          rules.add(bmgr.not(bmgr.and(upwardDiagonalQueen.get(i), upwardDiagonalQueen.get(j))));
        }
      }
    }
    return rules;
  }

  /**
   * Returns a boolean value indicating whether a queen is placed on the cell corresponding to the
   * given row and column.
   *
   * @param symbols a 2D BooleanFormula array representing the cells of the chess board.
   * @param model the Model object representing the current state of the board.
   * @param row the row index of the cell to check.
   * @param col the column index of the cell to check.
   * @return true if a queen is placed on the cell, false otherwise.
   */
  private boolean getValue(BooleanFormula[][] symbols, Model model, int row, int col) {
    return Boolean.TRUE.equals(model.evaluate(symbols[row][col]));
  }

  private void addConstraints(ProverEnvironment prover, BooleanFormula[][] symbols) throws InterruptedException, SolverException{
    List<BooleanFormula> rules =
            ImmutableList.<BooleanFormula>builder()
                    .addAll(rowRule1(symbols))
                    .addAll(rowRule2(symbols))
                    .addAll(columnRule(symbols))
                    .addAll(diagonalRule(symbols))
                    .build();
    prover.addConstraint(bmgr.and(rules));
  }

  private int enumerateSolutionsClassic(ProverEnvironment prover) throws InterruptedException, SolverException {
    BooleanFormula[][] symbols = getSymbols();
    // Add full Nqueens encoding
    List<BooleanFormula> rules =
            ImmutableList.<BooleanFormula>builder()
                    .addAll(rowRule1(symbols))
                    .addAll(rowRule2(symbols))
                    .addAll(columnRule(symbols))
                    .addAll(diagonalRule(symbols))
                    .build();
    prover.addConstraint(bmgr.and(rules));

    // Enumerate all solutions by iteratively adding blocking clauses
    int numSolutions = 0;
    while (!prover.isUnsat()) {
      var assignments = prover.getModelAssignments();
      BooleanFormula modelFormula = bmgr.makeTrue();
      for (var assgn : assignments) {
        modelFormula = bmgr.and(modelFormula, assgn.getAssignmentAsFormula());
      }
      prover.addConstraint(bmgr.not(modelFormula));
      numSolutions++;
    }
    return numSolutions;
  }

  private int enumerateSolutionsWithPropagator(ProverEnvironment prover) throws InterruptedException, SolverException {
    BooleanFormula[][] symbols = getSymbols();
    // Add full Nqueens encoding
    List<BooleanFormula> rules =
            ImmutableList.<BooleanFormula>builder()
                    .addAll(rowRule1(symbols))
                    .addAll(rowRule2(symbols))
                    .addAll(columnRule(symbols))
                    .addAll(diagonalRule(symbols))
                    .build();
    prover.addConstraint(bmgr.and(rules));

    // Enumerate all solutions via a custom user propagator.
    NQueensEnumeratingPropagator enumeratingPropagator = new NQueensEnumeratingPropagator();
    Verify.verify(prover.registerUserPropagator(enumeratingPropagator));
    for (BooleanFormula[] symbolRow : symbols) {
      for (BooleanFormula symbol : symbolRow) {
        enumeratingPropagator.registerExpression(symbol);
      }
    }

    boolean isUnsat = prover.isUnsat();
    Verify.verify(isUnsat); // The propagator should make sure that the instance becomes unsat by eventually
    // blocking all models.

    return enumeratingPropagator.getNumOfSolutions();
  }

  private int enumerateSolutionsWithConstraintPropagator(ProverEnvironment prover) throws InterruptedException, SolverException {
    BooleanFormula[][] symbols = getSymbols();
    // Add partial Nqueens encoding (only enforce a queen per row)
    // The remaining constraints are enforced by the user propagator
    List<BooleanFormula> rules =
            ImmutableList.<BooleanFormula>builder()
                    .addAll(rowRule1(symbols))
                    //.addAll(rowRule2(symbols))
                    //.addAll(columnRule(symbols))
                    //.addAll(diagonalRule(symbols))
                    .build();
    prover.addConstraint(bmgr.and(rules));

    // Enumerate all solutions via a custom user propagator that enforces unique placement constraints.
    NQueensConstraintPropagator constraintPropagator = new NQueensConstraintPropagator(symbols, bmgr);
    Verify.verify(prover.registerUserPropagator(constraintPropagator));
    for (BooleanFormula[] symbolRow : symbols) {
      for (BooleanFormula symbol : symbolRow) {
        constraintPropagator.registerExpression(symbol);
      }
    }

    boolean isUnsat = prover.isUnsat();
    Verify.verify(isUnsat); // The propagator should make sure that the instance becomes unsat by eventually
    // blocking all models.

    return constraintPropagator.getNumOfSolutions();
  }

}
