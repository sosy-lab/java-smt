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
package org.sosy_lab.java_smt.solvers.princess;

import ap.SimpleAPI;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IBoolLit;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.INot;
import com.google.common.base.Preconditions;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import javax.annotation.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import scala.Option;

class PrincessTheoremProver extends PrincessAbstractProver<Void, IExpression>
    implements ProverEnvironment {

  PrincessTheoremProver(
      PrincessFormulaManager pMgr,
      PrincessFormulaCreator creator,
      SimpleAPI pApi,
      ShutdownNotifier pShutdownNotifier) {
    super(pMgr, creator, pApi, pShutdownNotifier);
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula constraint) {
    Preconditions.checkState(!closed);
    final IFormula t = (IFormula) mgr.extractInfo(constraint);
    assertedFormulas.peek().add(t);
    addConstraint0(t);
    return null;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    throw new UnsupportedOperationException();
  }

  @Override
  public <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);

    // unpack formulas to terms
    List<IFormula> importantFormulas = new ArrayList<>(important.size());
    for (BooleanFormula impF : important) {
      importantFormulas.add((IFormula) mgr.extractInfo(impF));
    }

    api.push();
    while (!isUnsat()) {
      shutdownNotifier.shutdownIfNecessary();

      IFormula newFormula = new IBoolLit(true); // neutral element for AND
      List<BooleanFormula> wrappedPartialModel = new ArrayList<>(important.size());
      for (final IFormula f : importantFormulas) {
        final Option<Object> value = api.evalPartial(f);
        if (value.isDefined()) {
          final boolean isTrueValue = (boolean) value.get();
          final IFormula newElement = isTrueValue ? f : new INot(f);

          wrappedPartialModel.add(mgr.encapsulateBooleanFormula(newElement));
          newFormula = new IBinFormula(IBinJunctor.And(), newFormula, newElement);
        }
      }
      callback.apply(wrappedPartialModel);

      // add negation of current formula to get a new model in next iteration
      addConstraint0(new INot(newFormula));
    }
    shutdownNotifier.shutdownIfNecessary();
    api.pop();

    wasLastSatCheckSat = false; // we do not know about the current state, thus we reset the flag.

    return callback.getResult();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("UNSAT cores not supported by Princess");
  }

  @Override
  protected Collection<? extends IExpression> getAssertedFormulas() {
    List<IExpression> result = new ArrayList<>();
    assertedFormulas.forEach(result::addAll);
    return result;
  }
}
