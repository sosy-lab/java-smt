// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Unlicense OR Apache-2.0 OR MIT

package org.sosy_lab.java_smt.example;

import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;
import java.util.logging.Level;
import javax.annotation.Nullable;
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
  private final List<BooleanFormula> rules = new ArrayList<>();

  private NQueens(SolverContext pContext, int n) {
    context = pContext;
    bmgr = context.getFormulaManager().getBooleanFormulaManager();
    this.n = n;
  }

  public static void main(String... args)
      throws InvalidConfigurationException, SolverException, InterruptedException {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();
    Solvers solver = Solvers.SMTINTERPOL;
    try (SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {
      try (Scanner sc = new Scanner(System.in, Charset.defaultCharset().name())) {
        // Takes input from the user for number of queens to be placed
        System.out.println("Enter the number of Queens to be " + "placed on the board:");
        int n = sc.nextInt();
        NQueens myQueen = new NQueens(context, n);
        Boolean[][] solutions = myQueen.solve();
        if (solutions == null) {
          System.out.println("No solutions found.");
        } else {
          System.out.println("Solution:");
          for (Boolean[] row : solutions) {
            for (Boolean col : row) {
              if (col) {
                System.out.print("Q ");
              } else {
                System.out.print("_ ");
              }
            }
            System.out.println();
          }
          System.out.println();
        }
      }
    } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {
      logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");
    } catch (UnsupportedOperationException e) {
      logger.logUserException(Level.INFO, e, e.getMessage());
    }
  }

  //prepare symbols: one symbol for each of the N*N cells.
  private BooleanFormula[][] getSymbols() {
    final BooleanFormula[][] symbols = new BooleanFormula[n][n];
    for (int row = 0; row < n; row++) {
      for (int col = 0; col < n; col++) {
        symbols[row][col] = bmgr.makeVariable("q_" + row + "_" + col);
      }
    }
    return symbols;
  }

  private List<BooleanFormula> rowRule1(BooleanFormula[][] symbols) {

    /**
     * Rule 1: At least one queen per row,
     * or we can say make sure that there are N Queens on the board
    */
    for (BooleanFormula[] rowSymbols : symbols) {
      List<BooleanFormula> clause = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        clause.add(rowSymbols[i]);
      }
      rules.add(bmgr.or(clause));
    }
    return rules;
  }

  private List<BooleanFormula> rowRule2(BooleanFormula[][] symbols) {
    /**
     * Rule 2: Add constraints to ensure that at most one queen is placed in each row.
     * For n=4:
     *   0123
     * 0 ----
     * 1 ----
     * 2 ----
     * 3 ----
     * We add a negation of the conjunction of all possible pairs of variables in each row.
     */
    for (BooleanFormula[] rowSymbol : symbols) {
      for (int j1 = 0; j1 < n; j1++) {
        for (int j2 = j1 + 1; j2 < n; j2++) {
          rules.add(bmgr.not(bmgr.and(rowSymbol[j1], rowSymbol[j2])));
        }
      }
    }
    return rules;
  }

  private List<BooleanFormula> columnRule(BooleanFormula[][] symbols) {
    /**
     *  Rule 3: Add constraints to ensure that at most one queen is placed in each column.
     * For n=4:
     *   0123
     * 0 ||||
     * 1 ||||
     * 2 ||||
     * 3 ||||
     * We add a negation of the conjunction of all possible pairs of variables in each column.
     */
    for (int j = 0; j < n; j++) {
      for (int i1 = 0; i1 < n; i1++) {
        for (int i2 = i1 + 1; i2 < n; i2++) {
          rules.add(bmgr.not(bmgr.and(symbols[i1][j], symbols[i2][j])));
        }
      }
    }
    return rules;
  }

  private List<BooleanFormula> diagonalRule(BooleanFormula[][] symbols) {
    /**
     * Rule 4: At most one queen per diagonal
     *transform the field (=symbols) from square shape into a (downwards/upwards directed)
     *rhombus that is embedded in a rectangle (=downwardDiagonal/upwardDiagonal)
     *For example for N=4 from this square:
     *  0123
     *0 xxxx
     *1 xxxx
     *2 xxxx
     *3 xxxx
     *to this rhombus/rectangle:
     *  0123
     *0 x---
     *1 xx--
     *2 xxx-
     *3 xxxx
     *4 -xxx
     *5 --xx
     *6 ---x
    */
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
   * getValue returns a Boolean value indicating whether a queen is placed on the cell corresponding
   * to the given row and column. We modify this method to return true if the queen is placed, false
   * otherwise.
   */
  private Boolean getValue(BooleanFormula[][] symbols, Model model, int row, int col) {
    return model.evaluate(symbols[row][col]);
  }

  /**
   * Solves the N-Queens problem for the given board size and returns a possible solution. Returns
   * <code>Null</code> if no solution exists.
   */
  @Nullable
  private Boolean[][] solve() throws InterruptedException, SolverException {
    BooleanFormula[][] symbols = getSymbols();
    List<BooleanFormula> rules = new ArrayList<>();
    rules.addAll(rowRule1(symbols));
    rules.addAll(rowRule2(symbols));
    rules.addAll(columnRule(symbols));
    rules.addAll(diagonalRule(symbols));
    // solve N-Queens
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(bmgr.and(rules));
      boolean isUnsolvable = prover.isUnsat();
      if (isUnsolvable) {
        return null;
      }
      // get model and convert it
      Boolean[][] solution = new Boolean[n][n];
      try (Model model = prover.getModel()) {
        for (int row = 0; row < n; row++) {
          for (int col = 0; col < n; col++) {
            solution[row][col] = getValue(symbols, model, row, col);
          }
        }
        return solution;
      }
    }
  }
}
