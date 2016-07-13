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
package org.sosy_lab.solver.smtinterpol;

import com.google.common.base.Preconditions;
import com.google.common.collect.Iterators;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

class SmtInterpolInterpolatingProver extends SmtInterpolBasicProver<String, String>
    implements InterpolatingProverEnvironment<String> {

  private final SmtInterpolFormulaManager mgr;
  private final SmtInterpolEnvironment env;

  private final Map<String, Term> annotatedTerms; // Collection of termNames

  SmtInterpolInterpolatingProver(SmtInterpolFormulaManager pMgr) {
    super(pMgr);
    mgr = pMgr;
    env = mgr.createEnvironment();
    annotatedTerms = new HashMap<>();
  }

  @Override
  public void pop() {
    for (String removed : assertedFormulas.peek()) {
      annotatedTerms.remove(removed);
    }
    super.pop();
  }

  @Override
  public String addConstraint(BooleanFormula f) {
    Preconditions.checkState(!isClosed());
    String termName = generateTermName();
    Term t = mgr.extractInfo(f);
    Term annotatedTerm = env.annotate(t, new Annotation(":named", termName));
    env.assertTerm(annotatedTerm);
    assertedFormulas.peek().add(termName);
    annotatedTerms.put(termName, t);
    return termName;
  }

  @Override
  public BooleanFormula getInterpolant(List<String> pTermNamesOfA)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!isClosed());

    // SMTInterpol is not able to handle the trivial cases
    // so we need to check them explicitly
    if (pTermNamesOfA.isEmpty()) {
      return mgr.getBooleanFormulaManager().makeBoolean(true);
    } else if (pTermNamesOfA.containsAll(annotatedTerms.keySet())) {
      return mgr.getBooleanFormulaManager().makeBoolean(false);
    }

    Set<String> termNamesOfA = new HashSet<>(pTermNamesOfA);

    // calc difference: termNamesOfB := assertedFormulas - termNamesOfA
    Set<String> termNamesOfB =
        annotatedTerms
            .keySet()
            .stream()
            .filter(n -> !termNamesOfA.contains(n))
            .collect(Collectors.toSet());

    // build 2 groups:  (and A1 A2 A3...) , (and B1 B2 B3...)
    Term termA = buildConjunctionOfNamedTerms(termNamesOfA);
    Term termB = buildConjunctionOfNamedTerms(termNamesOfB);

    return getInterpolant(termA, termB);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<Set<String>> partitionedTermNames)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!isClosed());

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
    Preconditions.checkState(!isClosed());

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
    Preconditions.checkState(!isClosed());
    // get interpolant of groups
    Term[] itp = env.getInterpolants(new Term[] {termA, termB});
    assert itp.length == 1; // 2 groups -> 1 interpolant

    return mgr.encapsulateBooleanFormula(itp[0]);
  }

  private Term buildConjunctionOfNamedTerms(Set<String> termNames) {
    Preconditions.checkState(!isClosed());
    Preconditions.checkArgument(!termNames.isEmpty());

    Term[] terms = new Term[termNames.size()];
    int i = 0;
    for (String termName : termNames) {
      terms[i] = env.term(termName);
      i++;
    }

    if (terms.length > 1) {
      return env.term("and", terms);
    } else {
      return Iterators.getOnlyElement(Iterators.forArray(terms));
    }
  }

  @Override
  public void close() {
    assertedFormulas.clear();
    annotatedTerms.clear();
    super.close();
  }

  @Override
  protected Collection<Term> getAssertedTerms() {
    return annotatedTerms.values();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Assumption-solving is not supported.");
  }
}
