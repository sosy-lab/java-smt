// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.Generator;

public class SolverlessProverEnvironment implements ProverEnvironment {
  SolverContext differentSolverContext;
  private final Queue<Runnable> operationQueue = new ArrayDeque<>();
  private int fakeSize = 0;
  private final ProverEnvironment prover;

  public SolverlessProverEnvironment(SolverLessContext solverContext, Set<ProverOptions> pOptions) {
    try {
      if (solverContext.getUsedSolverForSMTSolving().equals(Solvers.SOLVERLESS)) {
        throw new InvalidConfigurationException(
            "Used Solver must not be SolverLess! SolverLess has no SMT-Solving capabilities.");
      }
      Configuration config =
          Configuration.builder().setOption("solver.generateSMTLIB2", String.valueOf(true)).build();
      LogManager logger = BasicLogManager.create(config);
      ShutdownManager shutdown = ShutdownManager.create();
      differentSolverContext =
          SolverContextFactory.createSolverContext(
              config, logger, shutdown.getNotifier(), Solvers.Z3);
    } catch (Exception e) {
      throw new RuntimeException("Problem creating solver differentSolverContext", e);
    }
    try {
      prover = differentSolverContext.newProverEnvironment(pOptions.toArray(new ProverOptions[0]));
    } catch (Exception e) {
      throw new RuntimeException("Problem creating solver differentSolverContext", e);
    }
  }

  @Override
  public Void addConstraint(BooleanFormula constraint) {
    Generator.assembleConstraint(constraint); // formula is generated then reparsed and given to z3
    String smtlib2String =
        String.valueOf(Generator.getLines())
            .replaceAll("(?m)^\\(push \\d+\\)\\s*", "") // removes push and pop lines
            .replaceAll("(?m)^\\(pop \\d+\\)\\s*", "") // as it isn't supported by the parser
            .replaceAll("\\s+", " ")
            .trim();

    operationQueue.add(
        () -> {
          try {
            prover.addConstraint(
                differentSolverContext.getFormulaManager().universalParseFromString(smtlib2String));
          } catch (Exception pE) {
            throw new RuntimeException(pE);
          }
        });
    return null;
  }

  @Override
  public void push() throws InterruptedException {
    operationQueue.add(
        () -> {
          try {
            prover.push();
          } catch (Exception pE) {
            throw new RuntimeException(pE);
          }
        });
    fakeSize++;
  }

  @Override
  public void pop() {
    operationQueue.add(
        () -> {
          try {
            prover.pop();
          } catch (Exception pE) {
            throw new RuntimeException(pE);
          }
        });
    fakeSize = Math.max(0, fakeSize - 1);
  }

  @Override
  public int size() {
    return fakeSize;
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    while (!operationQueue.isEmpty()) {
      operationQueue.poll().run();
    }
    return prover.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    while (!operationQueue.isEmpty()) {
      operationQueue.poll().run();
    }
    return prover.isUnsatWithAssumptions(assumptions);
  }

  @Override
  public Model getModel() throws SolverException {
    return prover.getModel();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    while (!operationQueue.isEmpty()) {
      operationQueue.poll().run();
    }
    return prover.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    while (!operationQueue.isEmpty()) {
      operationQueue.poll().run();
    }
    return prover.unsatCoreOverAssumptions(assumptions);
  }

  @Override
  public void close() {
    prover.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    while (!operationQueue.isEmpty()) {
      operationQueue.poll().run();
    }
    return prover.allSat(callback, important);
  }
}
