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

package org.sosy_lab.java_smt.example;

import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.CVC4;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.CVC5;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.DREAL4;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.MATHSAT5;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.SMTINTERPOL;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.YICES2;
import static org.sosy_lab.java_smt.SolverContextFactory.Solvers.Z3;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.test.HardFormulaRationalGenerator;

/**
 * This example pits all solvers supporting rationals against each other in a race to solve the same
 * hard SMT problems. The "+" stands for one solved problem.
 */
public class SolverRace {

  private static final ImmutableSet<Solvers> SOLVERS_WITH_RATIONALS =
      ImmutableSet.of(CVC4, CVC5, DREAL4, MATHSAT5, SMTINTERPOL, YICES2, Z3);

  // the maximum difficulty of the generated formulas
  private static final int MAX_DIFFICULTY = 100;
  // the maximum time of a thread in seconds
  private static final int MAX_TIME = 5;

  public static void main(String[] args) throws Exception {
    for (Solvers solver : SOLVERS_WITH_RATIONALS) {
      System.out.println(solver + ": ");
      thread(
          () -> {
            for (int i = 7; i < MAX_DIFFICULTY; i++) {
              int finalI = i;
              Configuration config = Configuration.defaultConfiguration();
              LogManager logger = BasicLogManager.create(config);
              ShutdownNotifier notifier = ShutdownNotifier.createDummy();
              try (SolverContext context =
                      SolverContextFactory.createSolverContext(config, logger, notifier, solver);
                  BasicProverEnvironment<?> prover = context.newProverEnvironment()) {
                BooleanFormulaManager bfmgr =
                    context.getFormulaManager().getBooleanFormulaManager();
                RationalFormulaManager rfmgr =
                    context.getFormulaManager().getRationalFormulaManager();
                HardFormulaRationalGenerator gen = new HardFormulaRationalGenerator(rfmgr, bfmgr);
                BooleanFormula threadFormula = gen.generate(finalI);
                prover.push(threadFormula);
                Preconditions.checkState(prover.isUnsat());
                System.out.print("+");
              }
            }
            System.out.println();
          });
    }
    System.exit(0);
  }

  private SolverRace() {}
  ;

  private static void thread(Run runnable) {
    final ExecutorService runningThread = Executors.newSingleThreadExecutor();
    final List<Throwable> exceptionsList = Collections.synchronizedList(new ArrayList<>());
    Future<?> future =
        runningThread.submit(
            () -> {
              try {
                runnable.run();
              } catch (Throwable e) {
                exceptionsList.add(e);
              }
            });
    try {
      future.get(MAX_TIME, TimeUnit.SECONDS);
    } catch (TimeoutException e) {
      future.cancel(true);
      System.out.println();
    } catch (InterruptedException | ExecutionException e) {
      exceptionsList.add(e);
    } finally {
      runningThread.shutdownNow();
    }
    Preconditions.checkState(exceptionsList.isEmpty());
  }

  /** just a small lambda-compatible interface. */
  private interface Run {
    void run() throws SolverException, InterruptedException, InvalidConfigurationException;
  }
}
