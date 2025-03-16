// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.Generator;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.ParserException;

public class SolverlessProverEnvironment implements ProverEnvironment {
  SolverContext solverContext;
  SolverContext differentSolverContext;
  private final List<BooleanFormula> constraints = new ArrayList<>();
  private final ProverEnvironment prover;

  public SolverlessProverEnvironment(SolverLessContext solverContext, Set<ProverOptions> pOptions) {
    try {
      if (solverContext.getUsedSolverForSMTSolving().equals(Solvers.SOLVERLESS)) {
        throw new InvalidConfigurationException(
            "Used Solver must not be SolverLess! SolverLess has no SMT-Solving capabilities.");
      }
      differentSolverContext =
          SolverContextFactory.createSolverContext(solverContext.getUsedSolverForSMTSolving());
      this.solverContext = solverContext;
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
  public void pop() {
    constraints.remove(constraints.size() - 1);
  }

  @Override
  public Void addConstraint(BooleanFormula constraint) {
    constraints.add(constraint);
    return null;
  }

  @Override
  public void push() throws InterruptedException {
    constraints.add(constraints.get(constraints.size() - 1));
  }

  @Override
  public int size() {
    return constraints.size();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    for (BooleanFormula formula : constraints) {
      Generator.assembleConstraint(formula);
    }
    String smtlib2String = Generator.getSMTLIB2String();
    // GENERATED CONSTRAINTS
    BooleanFormula parsedFormula;
    try {
      parsedFormula = solverContext.getFormulaManager().universalParseFromString(smtlib2String);
    } catch (Exception e) {
      throw new ParserException("An Error occured while reparsing. ", e);
    }
    // REPARSED THEM
    prover.addConstraint(parsedFormula);
    return prover.isUnsat();
    // GIVEN THEM TO Z3
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    return prover.isUnsatWithAssumptions(assumptions);
  }

  @Override
  public Model getModel() throws SolverException {
    return prover.getModel();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    return prover.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    return prover.unsatCoreOverAssumptions(assumptions);
  }

  @Override
  public void close() {
    prover.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    return prover.allSat(callback, important);
  }
}
