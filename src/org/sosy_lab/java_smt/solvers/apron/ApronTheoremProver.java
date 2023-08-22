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

package org.sosy_lab.java_smt.solvers.apron;

import apron.Abstract1;
import apron.ApronException;
import apron.Tcons1;
import com.google.common.base.Preconditions;
import com.google.common.collect.Iterables;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import javax.annotation.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;

public class ApronTheoremProver extends AbstractProverWithAllSat<Void>
    implements ProverEnvironment {

  private Abstract1 abstract1;
  private final ApronSolverContext solverContext;

  private final List<Collection<ApronConstraint>> assertedFormulas = new ArrayList<>();

  protected ApronTheoremProver(
      Set pSet,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier,
      ApronSolverContext pApronSolverContext) throws ApronException {
    super(pSet, pBmgr, pShutdownNotifier);
    this.solverContext = pApronSolverContext;
    this.abstract1 = new Abstract1(pApronSolverContext.getManager(),
        pApronSolverContext.getFormulaCreator().getEnvironment());
    this.assertedFormulas.add(new LinkedHashSet<>());
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(assertedFormulas.size() > 1);
    assertedFormulas.remove(assertedFormulas.size() - 1);
  }

  @Override
  public @Nullable Void addConstraint(BooleanFormula constraint)
      throws InterruptedException {
    ApronConstraint apronConstraint = (ApronConstraint) constraint;
    addConstraintException(apronConstraint);
    return null;
  }

  private void addConstraintException(ApronConstraint pConstraint) {
    try {
      Tcons1[] consOld = abstract1.toTcons(solverContext.getManager());
      Tcons1[] newCons = new Tcons1[consOld.length + 1];
      int i = 0;
      for (Tcons1 c : consOld) {
        newCons[i] = c;
        i++;
      }
      newCons[consOld.length] = pConstraint.getConstraintNode();
      this.abstract1 = new Abstract1(solverContext.getManager(), newCons);
      Iterables.getLast(assertedFormulas).add(pConstraint);
    } catch (ApronException e) {
      throw new RuntimeException(e);
    }
  }

  @Override
  public void push() throws InterruptedException {
    Preconditions.checkState(!closed);
    assertedFormulas.add(new LinkedHashSet<>());
  }

  @Override
  public int size() {
    return assertedFormulas.size() - 1;
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    return isUnsatApron();
  }

  private boolean isUnsatApron() {
    try {
      return abstract1.isBottom(solverContext.getManager());
    } catch (ApronException pApronException) {
      throw new RuntimeException(pApronException);
    }
  }

  @Override
  public Model getModel() throws SolverException {
    return new ApronModel(this, solverContext.getFormulaCreator(), getAssertedExpressions());
  }

  private Collection<ApronConstraint> getAssertedExpressions() {
    List<ApronConstraint> result = new ArrayList<>();
    assertedFormulas.forEach(result::addAll);
    return result;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    return null;
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(Collection assumptions)
      throws SolverException, InterruptedException {
    return Optional.empty();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection assumptions)
      throws SolverException, InterruptedException {
    return false;
  }

  @Override
  protected Evaluator getEvaluatorWithoutChecks() throws SolverException {
    return null;
  }

  public Abstract1 getAbstract1() {
    return abstract1;
  }
}
