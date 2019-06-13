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
package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.UnsatCore;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import javax.annotation.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

public class CVC4TheoremProver extends CVC4AbstractProver<Void> implements ProverEnvironment {

  protected CVC4TheoremProver(CVC4FormulaCreator creator) {
    super(creator);
  }

  @Override
  public Void push(BooleanFormula pF) {
    push();
    return addConstraint(pF);
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula pF) {
    Preconditions.checkState(!closed);
    Expr exp = creator.extractInfo(pF);
    env.assertFormula(exp);
    return null;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    List<BooleanFormula> converted = new ArrayList<>();
    UnsatCore core = env.getUnsatCore();
    for (Expr aCore : core) {
      converted.add(creator.encapsulateBoolean(aCore));
    }
    return converted;
  }

  // @Override
  // public void close() {
  // Preconditions.checkState(!closed);
  // // smtEngine.delete();
  // closed = true;
  // }

  // @Override
  // public <T> T allSat(AllSatCallback<T> pCallback, List<BooleanFormula> pImportant)
  //     throws InterruptedException, SolverException {
  //   Preconditions.checkState(!closed);
  //   // Unpack formulas to terms.
  //   Expr[] importantFormulas = new Expr[pImportant.size()];
  //   int i = 0;
  //   for (BooleanFormula impF : pImportant) {
  //     importantFormulas[i++] = getCVC4Expr(impF);
  //   }
  //
  //   smtEngine.push();
  //
  //   while (!isUnsat()) {
  //     Expr[] valuesOfModel = new Expr[importantFormulas.length];
  //     CVC4Model model = new CVC4Model(smtEngine, creator, assertedFormulas);
  //
  //     for (int j = 0; j < importantFormulas.length; j++) {
  //       Object valueOfExpr = model.evaluateImpl(importantFormulas[j]);
  //
  //       if (valueOfExpr instanceof Boolean && !((Boolean) valueOfExpr)) {
  //         valuesOfModel[j] =
  //             getCVC4Expr(bfmgr.not(mgr.encapsulateBooleanFormula(importantFormulas[j])));
  //       } else {
  //         valuesOfModel[j] = importantFormulas[j];
  //       }
  //     }
  //
  //     List<BooleanFormula> wrapped =
  //         Lists.transform(Arrays.asList(valuesOfModel), creator.encapsulateBoolean);
  //     pCallback.apply(wrapped);
  //
  //     BooleanFormula negatedModel = bfmgr.not(bfmgr.and(wrapped));
  //     smtEngine.assertFormula(getCVC4Expr(negatedModel));
  //   }
  //
  //   // we pushed some levels on assertionStack, remove them and delete solver
  //   smtEngine.pop();
  //   return pCallback.getResult();
  // }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  public <T> T allSat(AllSatCallback<T> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }


  @Override
  protected CVC4Model getCVC4Model() {
    return getModel();
  }
}
