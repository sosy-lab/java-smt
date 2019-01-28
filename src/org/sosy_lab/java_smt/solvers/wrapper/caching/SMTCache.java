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
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;

public interface SMTCache {

  /**
   * FIXME: For Allsat some strategy has yet to be thought of, to handle the generic callback
   */

  public enum CachingMode {
    IN_MEMORY;
  }

  public static SMTCache newSMTCache(CachingMode pMode) {
    SMTCache cache = null;

    switch (pMode) {
      case IN_MEMORY:
        cache = new InMemorySMTCache();
        break;
      default:
        // no-op. just return null
    }

    return cache;
  }

  public Boolean storeFormulaUnsat(BooleanFormula pFormula, boolean pUnsat);

  public Boolean isFormulaUnsat(BooleanFormula pFormula);

  public Boolean storeFormulaUnsatWithAssumptions(
      BooleanFormula pFormula,
      boolean pUnsat,
      Collection<BooleanFormula> pAssumptions);

  public Boolean isFormulaUnsatWithAssumptions(
      BooleanFormula pFormula,
      Collection<BooleanFormula> pAssumptions);

  public Model storeFormulaModel(BooleanFormula pFormula, Model pModel);

  public Model getFormulaModel(BooleanFormula pFormula);

  public ImmutableList<ValueAssignment> storeFormulaModelAssignments(
      BooleanFormula pFormula,
      ImmutableList<ValueAssignment> pAssignments);

  public ImmutableList<ValueAssignment> getFormulaModelAssignments(BooleanFormula pFormula);

  public List<BooleanFormula>
      storeFormulaUnsatCore(BooleanFormula pFormula, List<BooleanFormula> pUnsatCore);

  public List<BooleanFormula> getFormulaUnsatCore(BooleanFormula pFormula);

  public Optional<List<BooleanFormula>> storeFormulaUnsatCoreOverAssumptions(
      BooleanFormula pFormula,
      Optional<List<BooleanFormula>> pUnsatCore,
      Collection<BooleanFormula> pAssumptions);

  public Optional<List<BooleanFormula>> getFormulaUnsatCoreOverAssumptions(
      BooleanFormula pFormula,
      Collection<BooleanFormula> pAssumptions);

  public BooleanFormula storeFormulaInterpolant(
      BooleanFormula pFormula,
      BooleanFormula pInterpolant,
      Collection<?> pFormulasOfA);

  public BooleanFormula getFormulaInterpolant(BooleanFormula pFormula, Collection<?> pFormulasOfA);

  public List<BooleanFormula> storeFormulaTreeInterpolants(
      BooleanFormula pFormula,
      List<BooleanFormula> pTreeInterpolants,
      List<? extends Collection<?>> pPartitionedFormulas,
      int[] pStartOfSubTree);

  public List<BooleanFormula> getFormulaTreeInterpolants(
      BooleanFormula pFormula,
      List<? extends Collection<?>> pPartitionedFormulas,
      int[] pStartOfSubTree);

  public Integer storeFormulaMaximize(BooleanFormula pFormula, Integer max, Formula pObjective);

  public Integer getFormulaMaximize(BooleanFormula pFormula, Formula pObjective);

  public Integer storeFormulaMinimize(BooleanFormula pFormula, Integer min, Formula pObjective);

  public Integer getFormulaMinimize(BooleanFormula pFormula, Formula pObjective);

  public Optional<Rational> storeFormulaUpper(
      BooleanFormula pFormula,
      Optional<Rational> pUpper,
      int pHandle,
      Rational pEpsilon);

  public Optional<Rational>
      getFormulaUpper(BooleanFormula pFormula, int pHandle, Rational pEpsilon);

  public Optional<Rational> storeFormulaLower(
      BooleanFormula pFormula,
      Optional<Rational> pLower,
      int pHandle,
      Rational pEpsilon);

  public Optional<Rational>
      getFormulaLower(BooleanFormula pFormula, int pHandle, Rational pEpsilon);
}
