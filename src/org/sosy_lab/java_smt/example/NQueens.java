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
* would update this part once I get the complete solution
 */

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
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
public class NQueens {
    public static void main(String... args)
        throws InvalidConfigurationException, SolverException, InterruptedException, IOException {
        Configuration config = Configuration.defaultConfiguration();
        LogManager logger = BasicLogManager.create(config);
        ShutdownNotifier notifier = ShutdownNotifier.createDummy();
        Solvers solver = Solvers.PRINCESS;
        try (SolverContext context = SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {
            /*
            The outer loop present here is used to check whether my constraints give out correct
            solution for any of the value on n upto 12
            */
            for (int n = 1; n <= 12; n++) {
                NQueensSolver MyQueen = new NQueen(context, n);
                Boolean[][] solutions = MyQueen.solve(n);
                if (solutions==null) {
                    System.out.println("No solutions found for " + n + " queens.");
                } else {
                    System.out.println("Solutions for " + n + " queens:");
                    for (Boolean[] sol : solutions) {
                        for (int row = 0; row < solutions.length; row++) {
                            for (int col = 0; col < solutions[0].length; col++) {
                                if (solutions[row][col]) {
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
            }
        } catch (InvalidConfigurationException | UnsatisfiedLinkError e) {
            logger.logUserException(Level.INFO, e, "Solver " + solver + " is not available.");
        } catch (UnsupportedOperationException e) {
            logger.logUserException(Level.INFO, e, e.getMessage());
        }
    }
}
abstract class NQueensSolver {

    private final SolverContext context;
    final BooleanFormulaManager bmgr;

    NQueensSolver(SolverContext pContext) {
        context = pContext;
        bmgr = context.getFormulaManager().getBooleanFormulaManager();
    }
    abstract BooleanFormula[][] getSymbols();
    abstract List<BooleanFormula> getRules(BooleanFormula[][] symbols, SolverContext context);
    abstract Boolean getValue(BooleanFormula[][] symbols, Model model, int row, int col);

    /**
     * Solves the N-Queens problem for the given board size and returns a possible solution.
     * Returns <code>Null</code> if no solution exists.
     */
    @Nullable
    public Boolean[][] solve(int n) throws InterruptedException, SolverException {
        BooleanFormula[][] symbols = getSymbols();
        List<BooleanFormula> rules = getRules(symbols, context);
        // solve N-Queens
        try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
            prover.push(bmgr.and(rules));
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
     * getRules is the method used to add constraints that ensure that no two queens are in the same
     * row, column, or diagonal.
     */
    @Override
    List<BooleanFormula> getRules(BooleanFormula[][] symbols, SolverContext context) {
        List<BooleanFormula> rules = new ArrayList<>();

        // Add constraints to ensure that only one queen is placed in each row
        for (int row = 0; row < n; row++) {
            List<BooleanFormula> rowconstraint = new ArrayList<>();
            for (int col1 = 0; col1 < n; col1++) {
                for (int col2 = col1 + 1; col2 < n; col2++) {
                    rowconstraint.add(bmgr.or(bmgr.not(symbols[row][col1]), bmgr.not(symbols[row][col2])));
                }
            }
            rules.add(bmgr.and(rowconstraint));
        }

        // Add constraints to ensure that only one queen is placed in each column
        for (int col = 0; col < n; col++) {
            List<BooleanFormula> colconstraint = new ArrayList<>();
            for (int row1 = 0; row1 < n; row1++) {
                for (int row2 = row1 + 1; row2 < n; row2++) {
                    colconstraint.add(bmgr.or(bmgr.not(symbols[row1][col]), bmgr.not(symbols[row2][col])));
                }
            }
            rules.add(bmgr.and(colconstraint));
        }
        // Add constraints to ensure that at most one queen is placed in each diagonal
        for (int i = -n + 1; i < n; i++) {
            List<BooleanFormula> ors1 = new ArrayList<>();
            List<BooleanFormula> ors2 = new ArrayList<>();
            List<BooleanFormula> ors3 = new ArrayList<>();
            List<BooleanFormula> ors4 = new ArrayList<>();
            for (int j = 0; j < n; j++) {
                if (j + i >= 0 && j + i < n) {
                    ors1.add(symbols[j+i][j]);
                    ors2.add(symbols[j][j+i]);
                    ors3.add(bmgr.or(symbols[j+i][j], symbols[j][j+i]));
                }
                if (j - i >= 0 && j - i < n) {
                    ors1.add(symbols[j-i][j]);
                    ors2.add(symbols[j][j-i]);
                    ors4.add(bmgr.or(symbols[j-i][j], symbols[j][j-i]));
                }

                int x1 = i + j;
                int x2 = n - 1 - i + j;
                if (x1 >= 0 && x1 < n && x2 >= 0 && x2 < n) {
                    ors3.add(bmgr.or(symbols[i][j], symbols[x1][x1]));
                    ors4.add(bmgr.or(symbols[i][j], symbols[x2][n-1-x2]));
                }
            }
            rules.add(bmgr.or(ors1));
            rules.add(bmgr.or(ors2));
            rules.add(bmgr.or(ors3));
            rules.add(bmgr.or(ors4));
        }

        return rules;
    }
    /**
     * getValue returns a Boolean value indicating whether a queen is placed on the cell
     * corresponding to the given row and column.
     * We modify this method to return true if the queen is placed, false otherwise.
     */
    @Override
    Boolean getValue(BooleanFormula[][] symbols, Model model, int row, int col) {
        return model.evaluate(symbols[row][col]);
    }
}





