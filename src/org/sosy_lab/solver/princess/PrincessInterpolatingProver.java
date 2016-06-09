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

import static com.google.common.base.Predicates.in;
import static com.google.common.base.Predicates.not;
import static com.google.common.collect.FluentIterable.from;

import ap.parser.IExpression;
import ap.parser.IFormula;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.basicimpl.FormulaCreator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

class PrincessInterpolatingProver extends PrincessAbstractProver<Integer, Integer>
    implements InterpolatingProverEnvironment<Integer> {

  private final Map<Integer, IFormula> annotatedTerms = new HashMap<>(); // Collection of termNames
  private static final UniqueIdGenerator counter = new UniqueIdGenerator(); // for different indices

  PrincessInterpolatingProver(
      PrincessFormulaManager pMgr,
      FormulaCreator<
              IExpression, PrincessTermType, PrincessEnvironment, PrincessFunctionDeclaration>
          creator) {

    super(pMgr, true, creator);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    for (Integer removed : assertedFormulas.peek()) {
      annotatedTerms.remove(removed);
    }
    super.pop();
  }

  @Override
  public Integer addConstraint(BooleanFormula f) {
    Preconditions.checkState(!closed);
    int termIndex = counter.getFreshId();
    IFormula t = (IFormula) mgr.extractInfo(f);
    stack.assertTermInPartition(t, termIndex);

    assertedFormulas.peek().add(termIndex);
    annotatedTerms.put(termIndex, t);
    return termIndex;
  }

  @Override
  public BooleanFormula getInterpolant(List<Integer> pTermNamesOfA) {
    Preconditions.checkState(!closed);
    Set<Integer> indexesOfA = new HashSet<>(pTermNamesOfA);

    // calc difference: termNamesOfB := assertedFormulas - termNamesOfA
    Set<Integer> indexesOfB = from(annotatedTerms.keySet()).filter(not(in(indexesOfA))).toSet();

    // get interpolant of groups
    List<IFormula> itp = stack.getInterpolants(ImmutableList.of(indexesOfA, indexesOfB));
    assert itp.size() == 1; // 2 groups -> 1 interpolant

    return mgr.encapsulateBooleanFormula(itp.get(0));
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(final List<Set<Integer>> pTermNamesOfA) {
    Preconditions.checkState(!closed);

    // get interpolant of groups
    final List<IFormula> itps = stack.getInterpolants(pTermNamesOfA);

    final List<BooleanFormula> result = new ArrayList<>();
    for (final IFormula itp : itps) {
      result.add(mgr.encapsulateBooleanFormula(itp));
    }
    return result;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<Set<Integer>> partitionedFormulas, int[] startOfSubTree) {
    throw new UnsupportedOperationException(
        "Direct generation of tree interpolants is not supported.\n"
            + "Use another solver or another strategy for interpolants.");
  }

  @Override
  protected Collection<? extends IExpression> getAssertedFormulas() {
    return annotatedTerms.values();
  }
}
