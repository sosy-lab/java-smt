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

import static com.google.common.base.Predicates.in;
import static com.google.common.base.Predicates.not;
import static com.google.common.collect.FluentIterable.from;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.Model;
import org.sosy_lab.solver.api.Model.ValueAssignment;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

class SmtInterpolInterpolatingProver implements InterpolatingProverEnvironment<String> {

  protected final SmtInterpolFormulaManager mgr;
  private final SmtInterpolEnvironment env;

  private final List<String> assertedFormulas; // Collection of termNames
  private final Map<String, Term> annotatedTerms; // Collection of termNames

  // Set to "true" after closing.
  private boolean closed = false;
  private static final String PREFIX = "term_"; // for termnames
  private static final UniqueIdGenerator termIdGenerator =
      new UniqueIdGenerator(); // for different termnames

  SmtInterpolInterpolatingProver(SmtInterpolFormulaManager pMgr) {
    mgr = pMgr;
    env = mgr.createEnvironment();
    assertedFormulas = new ArrayList<>();
    annotatedTerms = new HashMap<>();
  }

  @Override
  public String push(BooleanFormula f) {
    push();
    return addConstraint(f);
  }

  protected void pushAndAssert(Term annotatedTerm) {
    Preconditions.checkState(!closed);
    push();
    env.assertTerm(annotatedTerm);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    String removed = assertedFormulas.remove(assertedFormulas.size() - 1); // remove last term
    annotatedTerms.remove(removed);
    assert assertedFormulas.size() == annotatedTerms.size();
    env.pop(1);
  }

  @Override
  public String addConstraint(BooleanFormula f) {
    Preconditions.checkState(!closed);
    String termName = generateTermName();
    Term t = mgr.extractInfo(f);
    Term annotatedTerm = env.annotate(t, new Annotation(":named", termName));
    env.assertTerm(annotatedTerm);
    assertedFormulas.add(termName);
    annotatedTerms.put(termName, t);
    assert assertedFormulas.size() == annotatedTerms.size();
    return termName;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    env.push(1);
  }

  @Override
  public boolean isUnsat() throws InterruptedException {
    Preconditions.checkState(!closed);
    return !env.checkSat();
  }

  @Override
  public BooleanFormula getInterpolant(List<String> pTermNamesOfA)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);

    Set<String> termNamesOfA = new HashSet<>(pTermNamesOfA);

    // calc difference: termNamesOfB := assertedFormulas - termNamesOfA
    Set<String> termNamesOfB = from(assertedFormulas).filter(not(in(termNamesOfA))).toSet();

    // build 2 groups:  (and A1 A2 A3...) , (and B1 B2 B3...)
    Term termA = buildConjunctionOfNamedTerms(termNamesOfA);
    Term termB = buildConjunctionOfNamedTerms(termNamesOfB);

    return getInterpolant(termA, termB);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<Set<String>> partitionedTermNames)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);

    final Term[] formulas = new Term[partitionedTermNames.size()];
    for (int i = 0; i < formulas.length; i++) {
      formulas[i] = buildConjunctionOfNamedTerms(partitionedTermNames.get(i));
    }

    // get interpolants of groups
    final Term[] itps = env.getInterpolants(formulas);

    final List<BooleanFormula> result = new ArrayList<>();
    for (Term itp : itps) {
      result.add(mgr.encapsulateBooleanFormula(itp));
    }
    return result;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<Set<String>> partitionedTermNames, int[] startOfSubTree)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);

    final Term[] formulas = new Term[partitionedTermNames.size()];
    for (int i = 0; i < formulas.length; i++) {
      formulas[i] = buildConjunctionOfNamedTerms(partitionedTermNames.get(i));
    }

    assert checkSubTrees(partitionedTermNames, startOfSubTree);

    // get interpolants of groups
    final Term[] itps = env.getTreeInterpolants(formulas, startOfSubTree);

    final List<BooleanFormula> result = new ArrayList<>();
    for (Term itp : itps) {
      result.add(mgr.encapsulateBooleanFormula(itp));
    }
    return result;
  }

  /** checks for a valid subtree-structure.
   * This code is taken from SMTinterpol itself, where it is disabled. */
  private static boolean checkSubTrees(
      List<Set<String>> partitionedTermNames, int[] startOfSubTree) {
    for (int i = 0; i < partitionedTermNames.size(); i++) {
      if (startOfSubTree[i] < 0) {
        throw new AssertionError("subtree array must not contain negative element");
      }
      int j = i;
      while (startOfSubTree[i] < j) {
        j = startOfSubTree[j - 1];
      }
      if (startOfSubTree[i] != j) {
        throw new AssertionError("malformed subtree array.");
      }
    }
    if (startOfSubTree[partitionedTermNames.size() - 1] != 0) {
      throw new AssertionError("malformed subtree array.");
    }

    return true;
  }

  protected BooleanFormula getInterpolant(Term termA, Term termB)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    // get interpolant of groups
    Term[] itp = env.getInterpolants(new Term[] {termA, termB});
    assert itp.length == 1; // 2 groups -> 1 interpolant

    return mgr.encapsulateBooleanFormula(itp[0]);
  }

  private Term buildConjunctionOfNamedTerms(Set<String> termNames) {
    Preconditions.checkState(!closed);
    Term[] terms = new Term[termNames.size()];
    int i = 0;
    for (String termName : termNames) {
      terms[i] = env.term(termName);
      i++;
    }
    if (terms.length > 1) {
      return env.term("and", terms);
    } else {
      assert terms.length != 0;
      return terms[0];
    }
  }

  @Override
  public void close() {
    Preconditions.checkState(!closed);
    assert assertedFormulas.size() == annotatedTerms.size();
    if (!assertedFormulas.isEmpty()) {
      env.pop(env.getStackDepth());
      assertedFormulas.clear();
      annotatedTerms.clear();
    }
    closed = true;
  }

  @Override
  public Model getModel() {
    Preconditions.checkState(!closed);
    assert assertedFormulas.size() == annotatedTerms.size();

    return new SmtInterpolModel(env.getModel(), mgr.getFormulaCreator(), annotatedTerms.values());
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    try (Model model = getModel()) {
      return ImmutableList.copyOf(model);
    }
  }

  private static String generateTermName() {
    return PREFIX + termIdGenerator.getFreshId();
  }
}
