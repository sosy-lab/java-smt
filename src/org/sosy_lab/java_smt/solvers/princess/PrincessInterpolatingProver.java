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

import static scala.collection.JavaConversions.asJavaIterable;
import static scala.collection.JavaConversions.asScalaSet;

import ap.SimpleAPI;
import ap.parser.IFormula;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import scala.collection.Seq;
import scala.collection.mutable.ArrayBuffer;

class PrincessInterpolatingProver extends PrincessAbstractProver<Integer, Integer>
    implements InterpolatingProverEnvironment<Integer> {

  private final Map<Integer, IFormula> annotatedTerms = new HashMap<>(); // Collection of termNames
  private static final UniqueIdGenerator counter = new UniqueIdGenerator(); // for different indices

  PrincessInterpolatingProver(
      PrincessFormulaManager pMgr,
      PrincessFormulaCreator creator,
      SimpleAPI pApi,
      ShutdownNotifier pShutdownNotifier) {
    super(pMgr, creator, pApi, pShutdownNotifier);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    assertedFormulas.peek().forEach(annotatedTerms::remove);
    super.pop();
  }

  @Override
  public Integer addConstraint(BooleanFormula f) {
    Preconditions.checkState(!closed);
    int termIndex = counter.getFreshId();
    IFormula t = (IFormula) mgr.extractInfo(f);

    // set partition number and add formula
    api.setPartitionNumber(termIndex);
    addConstraint0(t);

    // reset partition number to magic number -1,
    // which represents formulae belonging to all partitions.
    api.setPartitionNumber(-1);

    assertedFormulas.peek().add(termIndex);
    annotatedTerms.put(termIndex, t);
    return termIndex;
  }

  @Override
  public BooleanFormula getInterpolant(List<Integer> pTermNamesOfA) throws SolverException {
    Preconditions.checkState(!closed);
    Set<Integer> indexesOfA = ImmutableSet.copyOf(pTermNamesOfA);

    // calc difference: termNamesOfB := assertedFormulas - termNamesOfA
    Set<Integer> indexesOfB =
        annotatedTerms
            .keySet()
            .stream()
            .filter(f -> !indexesOfA.contains(f))
            .collect(ImmutableSet.toImmutableSet());

    // get interpolant of groups
    List<BooleanFormula> itp = getSeqInterpolants(ImmutableList.of(indexesOfA, indexesOfB));
    assert itp.size() == 1; // 2 groups -> 1 interpolant

    return itp.get(0);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(final List<Set<Integer>> partitions)
      throws SolverException {
    Preconditions.checkState(!closed);

    // convert to needed data-structure
    final ArrayBuffer<scala.collection.immutable.Set<Object>> args = new ArrayBuffer<>();
    for (Set<Integer> partition : partitions) {
      args.$plus$eq(asScalaSet(partition).toSet());
    }

    // do the hard work
    final Seq<IFormula> itps;
    try {
      itps = api.getInterpolants(args.toSeq(), api.getInterpolants$default$2());
    } catch (StackOverflowError e) {
      // Princess is recursive and thus produces stack overflows on large formulas.
      // Princess itself also catches StackOverflowError and returns "OutOfMemory" in checkSat(),
      // so we can do the same for getInterpolants().
      throw new SolverException(
          "Princess ran out of stack memory, try increasing the stack size.", e);
    }

    assert itps.length() == partitions.size() - 1
        : "There should be (n-1) interpolants for n partitions";

    // convert data-structure back
    // TODO check that interpolants do not contain abbreviations we did not introduce ourselves
    final List<BooleanFormula> result = new ArrayList<>();
    for (final IFormula itp : asJavaIterable(itps)) {
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
}
