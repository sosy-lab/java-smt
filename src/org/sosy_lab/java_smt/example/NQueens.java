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
        ShutdownNotifier notifier = ShutdownNotifier.createDummy();{
            Solvers solver = Solvers.SMTINTERPOL;
            try (SolverContext context =
                         SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {
                NQueensSolver MyQueen = new NQueen(context,4);
                Boolean[][] solution = MyQueen.solve(4);
                if (solution == null) {
                    System.out.println("The Queen can't be placed in this condition.");
                } else {
                    for (int row = 0; row < solution.length; row++) {
                        for (int col = 0; col < solution[0].length; col++) {
                            if (solution[row][col]) {
                                System.out.print("Q ");
                            } else {
                                System.out.print("_ ");
                            }
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
            List<BooleanFormula> ors = new ArrayList<>();
            for (int col = 0; col < n; col++) {
                ors.add(symbols[row][col]);
            }
            rules.add(bmgr.or(ors));
        }
        // Add constraints to ensure that only one queen is placed in each column
        for (int col = 0; col < n; col++) {
            List<BooleanFormula> ors = new ArrayList<>();
            for (int row = 0; row < n; row++) {
                ors.add(symbols[row][col]);
            }
            rules.add(bmgr.or(ors));
        }

        // Add constraints to ensure that only one queen is placed in each diagonal
        for (int i = 0; i < n; i++) {
            List<BooleanFormula> ors1 = new ArrayList<>();
            List<BooleanFormula> ors2 = new ArrayList<>();
            for (int j = 0; j < n; j++) {
                if (i + j < n) {
                    ors1.add(symbols[i + j][j]);
                    ors2.add(symbols[j][i + j]);
                }
                if (j - i >= 0) {
                    ors1.add(symbols[j - i][j]);
                    ors2.add(symbols[j][j - i]);
                }
            }
            rules.add(bmgr.or(ors1));
            rules.add(bmgr.or(ors2));
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





