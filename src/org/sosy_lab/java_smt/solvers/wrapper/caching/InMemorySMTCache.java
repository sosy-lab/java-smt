/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.wrapper.caching;

import com.google.common.collect.ImmutableList;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;

public class InMemorySMTCache implements SMTCache, Serializable {

  private static final long serialVersionUID = 1L;

  private final Map<Integer, Boolean> unsatMap = new HashMap<>();

  private final Map<Integer, Model> modelMap = new HashMap<>();

  private final Map<Integer, ImmutableList<ValueAssignment>> assignmentMap = new HashMap<>();

  private final Map<Integer, List<Formula>> usatCoreMap = new HashMap<>();

  private final Map<Integer, Formula> interpolantMap = new HashMap<>();

  private final Map<Integer, List<Formula>> treeInterpolantMap = new HashMap<>();

  private final Map<Integer, Rational> upperMap = new HashMap<>();

  private final Map<Integer, Rational> lowerMap = new HashMap<>();

  private final static int prime = 7;

  private Map<Integer, Integer> maxMap = new HashMap<>();

  private Map<Integer, Integer> minMap = new HashMap<>();

  @Override
  public Boolean storeFormulaUnsat(Formula pFormula, boolean pUnsat) {
    return unsatMap.put(pFormula.hashCode(), pUnsat);
  }

  @Override
  public Boolean isFormulaUnsat(Formula pFormula) {
    return unsatMap.get(pFormula.hashCode());
  }

  @Override
  public Boolean storeFormulaUnsatWithAssumptions(
      Formula pFormula,
      boolean pUnsat,
      Collection<Formula> pAssumptions) {
    return unsatMap.put(pFormula.hashCode() + prime * pAssumptions.hashCode(), pUnsat);
  }

  @Override
  public Boolean isFormulaUnsatWithAssumptions(
      Formula pFormula,
      Collection<Formula> pAssumptions) {
    return unsatMap.get(pFormula.hashCode() + prime * pAssumptions.hashCode());
  }

  @Override
  public Model storeFormulaModel(Formula pFormula, Model pModel) {
    return modelMap.put(pFormula.hashCode(), pModel);
  }

  @Override
  public Model getFormulaModel(Formula pFormula) {
    return modelMap.get(pFormula.hashCode());
  }

  @Override
  public ImmutableList<ValueAssignment> storeFormulaModelAssignments(
      Formula pFormula,
      ImmutableList<ValueAssignment> pAssignments) {
    return assignmentMap.put(pFormula.hashCode(), pAssignments);
  }

  @Override
  public ImmutableList<ValueAssignment> getFormulaModelAssignments(Formula pFormula) {
    return assignmentMap.get(pFormula.hashCode());
  }

  @Override
  public List<Formula> storeFormulaUnsatCore(Formula pFormula, List<Formula> pUnsatCore) {
    return usatCoreMap.put(pFormula.hashCode(), pUnsatCore);
  }

  @Override
  public List<Formula> getFormulaUnsatCore(Formula pFormula) {
    return usatCoreMap.get(pFormula.hashCode());
  }

  @Override
  public Optional<List<Formula>> storeFormulaUnsatCoreOverAssumptions(
      Formula pFormula,
      Optional<List<Formula>> pUnsatCore,
      Collection<Formula> pAssumptions) {
    Collection<Formula> unsatCore = null;
    if (pUnsatCore.isPresent()) {
      unsatCore = pUnsatCore.get();
    }
    unsatCore =
        usatCoreMap
            .put(pFormula.hashCode() + prime * pAssumptions.hashCode(), new ArrayList<>(unsatCore));
    return optionalList(unsatCore);
  }

  @Override
  public Optional<List<Formula>>
      getFormulaUnsatCoreOverAssumptions(Formula pFormula, Collection<Formula> pAssumptions) {
    Collection<Formula> unsatCore =
        usatCoreMap.get(pFormula.hashCode() + prime * pAssumptions.hashCode());
    return optionalList(unsatCore);
  }

  private Optional<List<Formula>> optionalList(Collection<Formula> unsatCore) {
    if (unsatCore != null) {
      return Optional.of(new ArrayList<>(unsatCore));
    } else {
      return Optional.empty();
    }
  }

  @Override
  public Formula storeFormulaInterpolant(
      Formula pFormula,
      Formula pInterpolant,
      Collection<?> pFormulasOfA) {
    return interpolantMap.put(pFormula.hashCode() + prime * pFormulasOfA.hashCode(), pInterpolant);
  }

  @Override
  public Formula getFormulaInterpolant(Formula pFormula, Collection<?> pFormulasOfA) {
    return interpolantMap.get(pFormula.hashCode() + prime * pFormulasOfA.hashCode());
  }

  @Override
  public List<Formula> storeFormulaTreeInterpolants(
      Formula pFormula,
      List<Formula> pTreeInterpolants,
      List<? extends Collection<?>> pPartitionedFormulas,
      int[] pStartOfSubTree) {
    int key = pFormula.hashCode();
    key += prime * pPartitionedFormulas.hashCode();
    key += prime * Arrays.hashCode(pStartOfSubTree);
    return treeInterpolantMap.put(key, pTreeInterpolants);
  }

  @Override
  public List<Formula> getFormulaTreeInterpolants(
      Formula pFormula,
      List<? extends Collection<?>> pPartitionedFormulas,
      int[] pStartOfSubTree) {
    int key = pFormula.hashCode();
    key += prime * pPartitionedFormulas.hashCode();
    key += prime * Arrays.hashCode(pStartOfSubTree);
    return treeInterpolantMap.get(key);
  }

  @Override
  public Integer storeFormulaMaximize(Formula pFormula, Integer pMax, Formula pObjective) {
    return maxMap.put(pFormula.hashCode(), pMax);
  }

  @Override
  public Integer getFormulaMaximize(Formula pFormula, Formula pObjective) {
    return maxMap.get(pFormula.hashCode());
  }

  @Override
  public Integer storeFormulaMinimize(Formula pFormula, Integer pMin, Formula pObjective) {
    return minMap.put(pFormula.hashCode(), pMin);
  }

  @Override
  public Integer getFormulaMinimize(Formula pFormula, Formula pObjective) {
    return minMap.get(pFormula.hashCode());
  }

  @Override
  public Optional<Rational> storeFormulaUpper(
      Formula pFormula,
      Optional<Rational> pUpper,
      int pHandle,
      Rational pEpsilon) {
    int key = pFormula.hashCode();
    key += prime * pEpsilon.hashCode();
    key += prime * pHandle;
    Rational last = null;
    if (pUpper.isPresent()) {
      last = upperMap.put(key, pUpper.get());
    }
    return Optional.ofNullable(last);
  }

  @Override
  public Optional<Rational>
      getFormulaUpper(Formula pFormula, int pHandle, Rational pEpsilon) {
    int key = pFormula.hashCode();
    key += prime * pEpsilon.hashCode();
    key += prime * pHandle;
    Rational value = upperMap.get(key);
    return Optional.ofNullable(value);
  }

  @Override
  public Optional<Rational> storeFormulaLower(
      Formula pFormula,
      Optional<Rational> pLower,
      int pHandle,
      Rational pEpsilon) {
    int key = pFormula.hashCode();
    key += prime * pEpsilon.hashCode();
    key += prime * pHandle;
    Rational last = null;
    if (pLower.isPresent()) {
      last = lowerMap.put(key, pLower.get());
    }
    return Optional.ofNullable(last);
  }

  @Override
  public Optional<Rational>
      getFormulaLower(Formula pFormula, int pHandle, Rational pEpsilon) {
    int key = pFormula.hashCode();
    key += prime * pEpsilon.hashCode();
    key += prime * pHandle;
    Rational value = lowerMap.get(key);
    return Optional.ofNullable(value);
  }

  @Override
  public void close() {
    // Nothing to do
  }
}