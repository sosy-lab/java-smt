package org.sosy_lab.java_smt.example;
/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
/*
*  The Output of this code
* The Queen can be placed in these ways:
0100
0001
1000
0010
* here '1' indicates position of queen that has been placed
 */

import com.google.common.base.Joiner;
import edu.umd.cs.findbugs.annotations.Nullable;
import java.io.IOException;
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
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
public class NQueens {
    public static void main(String... args)
            throws InvalidConfigurationException, SolverException, InterruptedException, IOException {
        Configuration config = Configuration.defaultConfiguration();
        LogManager logger = BasicLogManager.create(config);
        ShutdownNotifier notifier = ShutdownNotifier.createDummy();{
            Solvers solver = Solvers.PRINCESS;
            try (SolverContext context =
                         SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {
                NQueensSolver MyQueen = new NQueen(context,4);
                Boolean[][] solution = MyQueen.solve(4);
                if (solution == null) {
                    System.out.println("The Queen can't be placed in this condition.");
                } else {
                    System.out.println("The Queen can be placed in these ways:");
                    for (Boolean[] line : solution) {
                        System.out.println(Joiner.on("").join(line));
                    }
                }
            } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {

                logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");

            } catch (UnsupportedOperationException e) {
                logger.logUserException(Level.INFO, e, e.getMessage());
            }
        }
    }
}
abstract class NQueensSolver {

    private final SolverContext context;
    final BooleanFormulaManager bmgr;
    final IntegerFormulaManager imgr;
    NQueensSolver(SolverContext pContext) {
        context = pContext;
        bmgr = context.getFormulaManager().getBooleanFormulaManager();
        if (context.getSolverName() != Solvers.BOOLECTOR) {
            imgr = context.getFormulaManager().getIntegerFormulaManager();
        } else {
            imgr = null;
        }
    }
    abstract BooleanFormula[][] getSymbols();
    abstract List<BooleanFormula> getRules(BooleanFormula[][] symbols, SolverContext context);
    abstract List<BooleanFormula> getAssignments(BooleanFormula[][] symbols, int n);
    abstract Boolean getValue(BooleanFormula[][] symbols, Model model, int row, int col);

    /**
     * Solves the N-Queens problem for the given board size and returns a possible solution.
     * Returns <code>Null</code> if no solution exists.
     */
    @Nullable
    public Boolean[][] solve(int n) throws InterruptedException, SolverException {
        BooleanFormula[][] symbols = getSymbols();
        List<BooleanFormula> rules = getRules(symbols, context);
        List<BooleanFormula> assignments = getAssignments(symbols, n);

        // solve N-Queens
        try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
            prover.push(bmgr.and(rules));
            prover.push(bmgr.and(assignments));

            boolean isUnsolvable = prover.isUnsat();
            if (isUnsolvable) {
                return null;
            }

            // get model and convert it
            Boolean[][] solution = new Boolean[n][n] ;
            try (Model model = prover.getModel()) {
                for (int row = 0; row < n; row++) {
                    for (int col = 0; col < n; col++) {
                        solution[row][col] = getValue(symbols, model, row,col);
                    }
                }
                return solution;
            }
        }
    }
}
class NQueen extends NQueensSolver {
    private final int n;
    public NQueen(SolverContext context, int n) {
        super(context);
        this.n = n;
    }
    /**
     * prepare symbols: one symbol for each of the N*N cells.
     */
    @Override
    BooleanFormula[][] getSymbols() {
        final BooleanFormula[][] symbols = new BooleanFormula[n][n];
        for (int row = 0; row < n; row++) {
            for (int col = 0; col < n; col++) {
                symbols[row][col] = bmgr.makeVariable("q_" + row + "_" + col);
            }
        }
        return symbols;
    }
    /*
 getRules is the method used to add constraints that ensure that no two queens are in the same
 row, column, or diagonal.
 */
    @Override
    List<BooleanFormula> getRules(BooleanFormula[][] symbols, SolverContext context) {
        List<BooleanFormula> rules = new ArrayList<>();

        // Add constraints to ensure that only one queen is placed in each row
        for (int row = 0; row < n; row++) {
            BooleanFormula rowConstraint = bmgr.or(symbols[row]);
            rules.add(rowConstraint);
        }

        // Add constraints to ensure that only one queen is placed in each column
        for (int col = 0; col < n; col++) {
            BooleanFormula[] colSymbols = new BooleanFormula[n];
            for (int row = 0; row < n; row++) {
                colSymbols[row] = symbols[row][col];
            }
            BooleanFormula colConstraint = bmgr.or(colSymbols);
            rules.add(colConstraint);
        }

        // Add constraints to ensure that only one queen is placed in each diagonal
        for (int row = 0; row < n; row++) {
            for (int col = 0; col < n; col++) {
                // Check diagonals starting from the current position to the top-left corner
                List<BooleanFormula> diagSymbols = new ArrayList<>();
                for (int i = row, j = col; i >= 0 && j >= 0; i--, j--) {
                    diagSymbols.add(symbols[i][j]);
                }
                if (!diagSymbols.isEmpty()) {
                    BooleanFormula diagConstraint1 = bmgr.or(diagSymbols.toArray(new BooleanFormula[0]));
                    rules.add(diagConstraint1);
                }

                // Check diagonals starting from the current position to the bottom-right corner
                diagSymbols.clear();
                for (int i = row, j = col; i < n && j < n; i++, j++) {
                    diagSymbols.add(symbols[i][j]);
                }
                if (!diagSymbols.isEmpty()) {
                    BooleanFormula diagConstraint2 = bmgr.or(diagSymbols.toArray(new BooleanFormula[0]));
                    rules.add(diagConstraint2);
                }

                // Check diagonals starting from the current position to the top-right corner
                diagSymbols.clear();
                for (int i = row, j = col; i >= 0 && j < n; i--, j++) {
                    diagSymbols.add(symbols[i][j]);
                }
                if (!diagSymbols.isEmpty()) {
                    BooleanFormula diagConstraint3 = bmgr.or(diagSymbols.toArray(new BooleanFormula[0]));
                    rules.add(diagConstraint3);
                }

                // Check diagonals starting from the current position to the bottom-left corner
                diagSymbols.clear();
                for (int i = row, j = col; i < n && j >= 0; i++, j--) {
                    diagSymbols.add(symbols[i][j]);
                }
                if (!diagSymbols.isEmpty()) {
                    BooleanFormula diagConstraint4 = bmgr.or(diagSymbols.toArray(new BooleanFormula[0]));
                    rules.add(diagConstraint4);
                }
            }
        }
        return rules;
    }
    @Override
      /*
        getAssignments method is used to create constraints for the solver
    */
    List<BooleanFormula> getAssignments(BooleanFormula[][] symbols, int n) {
        final List<BooleanFormula> assignments = new ArrayList<>();

        // Add the row constraints
        for (int row = 0; row < n; row++) {
            List<BooleanFormula> rowFormula = new ArrayList<>();
            for (int col = 0; col < n; col++) {
                rowFormula.add(symbols[row][col]);
            }
            assignments.add(bmgr.or(rowFormula));
            assignments.add(bmgr.and(rowFormula));
        }

        // Add the column constraints
        for (int col = 0; col < n; col++) {
            List<BooleanFormula> colFormula = new ArrayList<>();
            for (int row = 0; row < n; row++) {
                colFormula.add(symbols[row][col]);
            }
            assignments.add(bmgr.or(colFormula));
            assignments.add(bmgr.and(colFormula));
        }

        // Add the diagonal constraints
        for (int i = 0; i < n; i++) {
            List<BooleanFormula> diag1Formula = new ArrayList<>();
            List<BooleanFormula> diag2Formula = new ArrayList<>();
            for (int j = 0; j < n; j++) {
                int r1 = j - i;
                int r2 = n - j - i - 1;
                if (r1 >= 0 && r1 < n) {
                    diag1Formula.add(symbols[r1][j]);
                }
                if (r2 >= 0 && r2 < n) {
                    diag2Formula.add(symbols[r2][j]);
                }
            }
            if (diag1Formula.size() > 0) {
                assignments.add(bmgr.or(diag1Formula));
                assignments.add(bmgr.and(diag1Formula));
            }
            if (diag2Formula.size() > 0) {
                assignments.add(bmgr.or(diag2Formula));
                assignments.add(bmgr.and(diag2Formula));
            }
        }

        return assignments;
    }
    @Override
    @org.checkerframework.checker.nullness.qual.Nullable
    Boolean getValue(BooleanFormula[][] symbols, Model model, int row, int col) {
        BooleanFormula symb=symbols[row][col];
        return model.evaluate(symb);
    }
    public BooleanFormula Equals(IntegerFormula a, IntegerFormula b) {
        return bmgr.and(
                imgr.lessOrEquals(a, b),
                imgr.lessOrEquals(b, a)
        );
    }
}





