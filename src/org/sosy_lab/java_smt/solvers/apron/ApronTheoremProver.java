// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.apron;

import apron.Abstract1;
import apron.ApronException;
import apron.Tcons1;
import apron.Texpr1Node;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;

public class ApronTheoremProver extends AbstractProverWithAllSat<Void>
    implements ProverEnvironment {

  private final ApronSolverContext solverContext;
  private final Logger logger = Logger.getLogger("TheoremProver logger");
  private Abstract1 abstract1;

  protected ApronTheoremProver(
      Set<ProverOptions> pSet,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier,
      ApronSolverContext pApronSolverContext)
      throws ApronException {
    super(pSet, pBmgr, pShutdownNotifier);
    this.solverContext = pApronSolverContext;
    this.abstract1 =
        new Abstract1(
            pApronSolverContext.getManager(),
            pApronSolverContext.getFormulaCreator().getFormulaEnvironment());
  }

  public ApronSolverContext getSolverContext() {
    return solverContext;
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    Preconditions.checkState(!closed);
    return super.getModelAssignments();
  }

  public boolean getClosed() {
    return closed;
  }

  @Override
  protected void popImpl() {
    // Do nothing
  }

  @Override
  protected @Nullable Void addConstraintImpl(BooleanFormula constraint)
      throws InterruptedException {
    ApronConstraint node = (ApronConstraint) ApronFormulaManager.getTerm(constraint);
    try {
      for (Map.Entry<Tcons1, Texpr1Node> cons : node.getConstraintNodes().entrySet()) {
        Tcons1[] consOld = abstract1.toTcons(solverContext.getManager());
        Tcons1[] newCons = new Tcons1[consOld.length + 1];
        int i = 0;
        for (Tcons1 c : consOld) {
          c.extendEnvironment(solverContext.getFormulaCreator().getFormulaEnvironment());
          newCons[i] = c;
          i++;
        }
        newCons[consOld.length] = cons.getKey();
        this.abstract1.changeEnvironment(
            solverContext.getManager(),
            solverContext.getFormulaCreator().getFormulaEnvironment(),
            false);
        this.abstract1 = new Abstract1(solverContext.getManager(), newCons);
      }
    } catch (ApronException e) {
      throw new RuntimeException(e);
    }
    return null;
  }

  @Override
  protected void pushImpl() throws InterruptedException {
    // Do nothing
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    try {
      if (abstract1.isBottom(solverContext.getManager())) {
        return true;
      } else {
        logger.setLevel(Level.WARNING);
        logger.warning(
            "Apron can only guarantee for clear results for UNSAT! SAT can "
                + "also mean UNKNOWN!");
        return false;
      }
    } catch (ApronException pApronException) {
      throw new RuntimeException(pApronException);
    }
  }

  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    ImmutableList.Builder<ApronConstraint> constraints = ImmutableList.builder();
    for (var f : getAssertedFormulas()) {
      constraints.add((ApronConstraint) ApronFormulaManager.getTerm(f));
    }
    return new ApronModel(this, solverContext.getFormulaCreator(), constraints.build());
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    throw new UnsupportedOperationException("Unsatcore not supported.");
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    throw new NullPointerException();
  }

  /**
   * with the help of the join() method form the Apron-library one can build a new abstract1 object
   * with additional constraints.
   *
   * @param assumptions A list of literals.
   * @return if the prover is satisfiable with some additional assumptions
   * @throws SolverException throws exception
   * @throws InterruptedException throws exception
   */
  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    List<Tcons1> constraints = new ArrayList<>();
    for (BooleanFormula assumption : assumptions) {
      ApronConstraint cons = (ApronConstraint) ApronFormulaManager.getTerm(assumption);
      for (Map.Entry<Tcons1, Texpr1Node> entry : cons.getConstraintNodes().entrySet()) {
        constraints.add(entry.getKey());
      }
    }
    Tcons1[] tcons1s = constraints.toArray(new Tcons1[constraints.size()]);
    try {
      Abstract1 absNew = new Abstract1(solverContext.getManager(), tcons1s);
      Abstract1 result = this.abstract1.joinCopy(solverContext.getManager(), absNew);
      return result.isBottom(solverContext.getManager());
    } catch (ApronException e) {
      throw new RuntimeException(e.toString());
    }
  }

  public Abstract1 getAbstract1() {
    return abstract1;
  }

  @Override
  protected Evaluator getEvaluatorWithoutChecks() throws SolverException {
    throw new UnsupportedOperationException("Apron does not support Evaluator without checks.");
  }

  @Override
  public void close() {
    if (!closed) {
      closed = true;
    }
    super.close();
  }
}
