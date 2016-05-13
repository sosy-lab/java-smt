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

import com.google.common.base.Optional;
import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.api.SolverContext.ProverOptions;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.annotation.Nullable;

class SmtInterpolTheoremProver extends SmtInterpolBasicProver<Void> implements ProverEnvironment {

  private final SmtInterpolFormulaManager mgr;
  private final SmtInterpolEnvironment env;
  private final List<Term> assertedTerms;
  private final Map<String, Term> annotatedTerms; // Collection of termNames
  private final FormulaCreator<Term, Sort, SmtInterpolEnvironment, FunctionSymbol> creator;
  private final boolean generateUnsatCores;

  // Next modification to assertion stack should pop before doing anything.
  private transient boolean shouldPop = false;

  SmtInterpolTheoremProver(
      SmtInterpolFormulaManager pMgr,
      FormulaCreator<Term, Sort, SmtInterpolEnvironment, FunctionSymbol> pCreator,
      Set<ProverOptions> options) {
    super(pMgr);
    mgr = pMgr;
    assertedTerms = new ArrayList<>();
    env = mgr.createEnvironment();
    creator = pCreator;
    checkNotNull(env);
    annotatedTerms = new HashMap<>();
    generateUnsatCores = options.contains(ProverOptions.GENERATE_UNSAT_CORE);
  }

  @Override
  public Void push(BooleanFormula f) {
    popIfNecessary();
    return super.push(f);
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    push(mgr.getBooleanFormulaManager().and(assumptions));
    boolean out = isUnsat();
    shouldPop = true;
    return out;
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {

    push();
    Preconditions.checkState(
        annotatedTerms.isEmpty(),
        "Empty environment required for UNSAT core" + " over assumptions.");
    for (BooleanFormula assumption : assumptions) {
      String termName = generateTermName();
      Term t = mgr.extractInfo(assumption);
      Term annotated = env.annotate(t, new Annotation(":named", termName));
      annotatedTerms.put(termName, t);
      env.assertTerm(annotated);
    }
    if (!isUnsat()) {
      return Optional.absent();
    }
    List<BooleanFormula> out = getUnsatCore();
    pop();
    return Optional.of(out);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    popIfNecessary();
    assertedTerms.remove(assertedTerms.size() - 1); // remove last term
    env.pop(1);
  }

  @Override
  @Nullable
  public Void addConstraint(BooleanFormula constraint) {
    Preconditions.checkState(!closed);
    popIfNecessary();
    Term t = mgr.extractInfo(constraint);
    if (generateUnsatCores) {
      String termName = generateTermName();
      Term annotated = env.annotate(t, new Annotation(":named", termName));
      annotatedTerms.put(termName, t);
      env.assertTerm(annotated);
    } else {
      env.assertTerm(t);
    }
    assertedTerms.add(t);
    return null;
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    popIfNecessary();
    if (env.getStackDepth() > 0) {
      env.pop(env.getStackDepth());
      assertedTerms.clear();
    }
    closed = true;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    Term[] terms = env.getUnsatCore();
    return Lists.transform(
        Arrays.asList(terms),
        input -> creator.encapsulateBoolean(annotatedTerms.get(input.toString())));
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
      callback.apply(Lists.transform(Arrays.asList(model), creator::encapsulateBoolean));
    }
    return callback.getResult();
  }

  private void popIfNecessary() {
    if (shouldPop) {
      shouldPop = false;
      pop();
    }
  }

  @Override
  protected Collection<Term> getAssertedTerms() {
    return assertedTerms;
  }
}
