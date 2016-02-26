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
package org.sosy_lab.solver.smtinterpol;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import javax.annotation.Nullable;

class SmtInterpolTheoremProver implements ProverEnvironment {

  private final SmtInterpolFormulaManager mgr;
  private final SmtInterpolEnvironment env;
  private final List<Term> assertedTerms;
  private final FormulaCreator<Term, Sort, SmtInterpolEnvironment> creator;
  private boolean closed = false;

  SmtInterpolTheoremProver(
      SmtInterpolFormulaManager pMgr, FormulaCreator<Term, Sort, SmtInterpolEnvironment> pCreator) {
    mgr = pMgr;
    assertedTerms = new ArrayList<>();
    env = mgr.createEnvironment();
    creator = pCreator;
    checkNotNull(env);
  }

  @Override
  public boolean isUnsat() throws InterruptedException {
    Preconditions.checkState(!closed);
    return !env.checkSat();
  }

  @Override
  public Model getModel() {
    Preconditions.checkState(!closed);
    return new SmtInterpolModel(env.getModel(), creator, assertedTerms);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    assertedTerms.remove(assertedTerms.size() - 1); // remove last term
    env.pop(1);
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula constraint) {
    Preconditions.checkState(!closed);
    Term t = mgr.extractInfo(constraint);
    assertedTerms.add(t);
    env.assertTerm(t);
    return null;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    env.push(1);
  }

  @Override
  public Void push(BooleanFormula f) {
    Preconditions.checkState(!closed);
    final Term t = mgr.extractInfo(f);
    assertedTerms.add(t);
    push();
    env.assertTerm(t);
    return null;
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    if (!assertedTerms.isEmpty()) {
      env.pop(env.getStackDepth());
      assertedTerms.clear();
    }
    closed = true;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    Term[] terms = env.getUnsatCore();
    return Lists.transform(Arrays.asList(terms), creator.encapsulateBoolean);
  }

  @Override
  public <T> T allSat(AllSatCallback<T> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    Term[] importantTerms = new Term[important.size()];
    int i = 0;
    for (BooleanFormula impF : important) {
      importantTerms[i++] = mgr.extractInfo(impF);
    }
    for (Term[] model : env.checkAllSat(importantTerms)) {
      callback.apply(Lists.transform(Arrays.asList(model), creator.encapsulateBoolean));
    }
    return callback.getResult();
  }
}
