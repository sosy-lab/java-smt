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

package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.common.collect.Collections3;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

abstract class SmtInterpolBasicProver<T, AF> implements BasicProverEnvironment<T> {

  private boolean closed = false;
  protected final SmtInterpolEnvironment env;
  protected final FormulaCreator<Term, Sort, SmtInterpolEnvironment, FunctionSymbol> creator;
  protected final SmtInterpolFormulaManager mgr;
  protected final Deque<List<AF>> assertedFormulas = new ArrayDeque<>();
  protected final Map<String, Term> annotatedTerms = new HashMap<>(); // Collection of termNames

  private static final String PREFIX = "term_"; // for termnames
  private static final UniqueIdGenerator termIdGenerator =
      new UniqueIdGenerator(); // for different termnames

  SmtInterpolBasicProver(SmtInterpolFormulaManager pMgr) {
    mgr = pMgr;
    env = pMgr.createEnvironment();
    creator = pMgr.getFormulaCreator();
  }

  protected boolean isClosed() {
    return closed;
  }

  @Override
  public final void push() {
    Preconditions.checkState(!closed);
    assertedFormulas.push(new ArrayList<>());
    env.push(1);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    assertedFormulas.pop();
    env.pop(1);
  }

  @Override
  public boolean isUnsat() throws InterruptedException {
    Preconditions.checkState(!closed);
    return !env.checkSat();
  }

  @Override
  public SmtInterpolModel getModel() {
    Preconditions.checkState(!closed);
    return new SmtInterpolModel(env.getModel(), creator, getAssertedTerms());
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    try (SmtInterpolModel model = getModel()) {
      return model.modelToList();
    }
  }

  protected static String generateTermName() {
    return PREFIX + termIdGenerator.getFreshId();
  }

  protected abstract Collection<Term> getAssertedTerms();

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!isClosed());
    Term[] terms = env.getUnsatCore();
    return Collections3.transformedImmutableListCopy(
        terms, input -> creator.encapsulateBoolean(annotatedTerms.get(input.toString())));
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws InterruptedException {
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
      return Optional.empty();
    }
    List<BooleanFormula> out = getUnsatCore();
    pop();
    return Optional.of(out);
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    assertedFormulas.clear();
    annotatedTerms.clear();
    env.pop(env.getStackDepth());
    closed = true;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Assumption-solving is not supported.");
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    Preconditions.checkState(!isClosed());
    Term[] importantTerms = new Term[important.size()];
    int i = 0;
    for (BooleanFormula impF : important) {
      importantTerms[i++] = mgr.extractInfo(impF);
    }
    for (Term[] model : env.checkAllSat(importantTerms)) {
      callback.apply(Collections3.transformedImmutableListCopy(model, creator::encapsulateBoolean));
    }
    return callback.getResult();
  }
}
