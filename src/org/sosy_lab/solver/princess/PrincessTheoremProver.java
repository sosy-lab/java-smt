/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.princess;

import static com.google.common.base.Preconditions.checkNotNull;

import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IBoolLit;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.INot;

import com.google.common.base.Optional;
import com.google.common.base.Preconditions;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.ProverEnvironment;

import scala.Option;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import javax.annotation.Nullable;

class PrincessTheoremProver extends PrincessAbstractProver<Void> implements ProverEnvironment {

  private final List<IExpression> assertedTerms = new ArrayList<>();
  private final ShutdownNotifier shutdownNotifier;

  PrincessTheoremProver(
      PrincessFormulaManager pMgr,
      ShutdownNotifier pShutdownNotifier,
      PrincessFormulaCreator creator) {
    super(pMgr, false, creator);
    this.shutdownNotifier = checkNotNull(pShutdownNotifier);
  }

  @Override
  public Model getModel() throws SolverException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(!isUnsat(), "model is only available for SAT environments");

    return new PrincessModel(stack.getPartialModel(), creator, assertedTerms);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    assertedTerms.remove(assertedTerms.size() - 1); // remove last term
    stack.pop(1);
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula constraint) {
    Preconditions.checkState(!closed);
    final IFormula t = (IFormula) mgr.extractInfo(constraint);
    assertedTerms.add(t);
    stack.assertTerm(t);
    return null;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    stack.push(1);
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    throw new UnsupportedOperationException();
  }

  @Override
  public <T> T allSat(ProverEnvironment.AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);

    // unpack formulas to terms
    List<IFormula> importantFormulas = new ArrayList<>(important.size());
    for (BooleanFormula impF : important) {
      importantFormulas.add((IFormula) mgr.extractInfo(impF));
    }

    stack.push(1);
    while (stack.checkSat()) {
      shutdownNotifier.shutdownIfNecessary();

      IFormula newFormula = new IBoolLit(true); // neutral element for AND
      List<BooleanFormula> wrappedPartialModel = new ArrayList<>(important.size());
      for (final IFormula f : importantFormulas) {
        final Option<Object> value = stack.evalPartial(f);
        if (value.isDefined()) {
          final boolean isTrueValue = (boolean) value.get();
          final IFormula newElement = isTrueValue ? f : new INot(f);

          wrappedPartialModel.add(mgr.encapsulateBooleanFormula(newElement));
          newFormula = new IBinFormula(IBinJunctor.And(), newFormula, newElement);
        }
      }
      callback.apply(wrappedPartialModel);

      // add negation of current formula to get a new model in next iteration
      stack.assertTerm(new INot(newFormula));
    }
    shutdownNotifier.shutdownIfNecessary();
    stack.pop(1);

    return callback.getResult();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    push(mgr.getBooleanFormulaManager().and(assumptions));
    boolean out = isUnsat();
    pop();
    return out;
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("UNSAT cores not supported by Princess");
  }
}
