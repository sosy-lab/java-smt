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
   * FIXME: For Allsat some strategy has yet to be thought of, to handle the generic callback.
   */

  enum CachingMode {
    IN_MEMORY,
    SIMPLE_BINARY;
  }

  static SMTCache newSMTCache(CachingMode pMode) {
    SMTCache cache = null;

    switch (pMode) {
      case IN_MEMORY:
        cache = new InMemorySMTCache();
        break;
      case SIMPLE_BINARY:
        cache = new SimpleBinarySMTCache();
        break;
      default:
        // no-op. just return null
    }

    return cache;
  }

  Boolean storeFormulaUnsat(BooleanFormula pFormula, boolean pUnsat);

  Boolean isFormulaUnsat(BooleanFormula pFormula);

  Boolean storeFormulaUnsatWithAssumptions(
      BooleanFormula pFormula,
      boolean pUnsat,
      Collection<BooleanFormula> pAssumptions);

  Boolean isFormulaUnsatWithAssumptions(
      BooleanFormula pFormula,
      Collection<BooleanFormula> pAssumptions);

  Model storeFormulaModel(BooleanFormula pFormula, Model pModel);

  Model getFormulaModel(BooleanFormula pFormula);

  ImmutableList<ValueAssignment> storeFormulaModelAssignments(
      BooleanFormula pFormula,
      ImmutableList<ValueAssignment> pAssignments);

  ImmutableList<ValueAssignment> getFormulaModelAssignments(BooleanFormula pFormula);

  List<BooleanFormula>
      storeFormulaUnsatCore(BooleanFormula pFormula, List<BooleanFormula> pUnsatCore);

  List<BooleanFormula> getFormulaUnsatCore(BooleanFormula pFormula);

  Optional<List<BooleanFormula>> storeFormulaUnsatCoreOverAssumptions(
      BooleanFormula pFormula,
      Optional<List<BooleanFormula>> pUnsatCore,
      Collection<BooleanFormula> pAssumptions);

  Optional<List<BooleanFormula>> getFormulaUnsatCoreOverAssumptions(
      BooleanFormula pFormula,
      Collection<BooleanFormula> pAssumptions);

  BooleanFormula storeFormulaInterpolant(
      BooleanFormula pFormula,
      BooleanFormula pInterpolant,
      Collection<?> pFormulasOfA);

  BooleanFormula getFormulaInterpolant(BooleanFormula pFormula, Collection<?> pFormulasOfA);

  List<BooleanFormula> storeFormulaTreeInterpolants(
      BooleanFormula pFormula,
      List<BooleanFormula> pTreeInterpolants,
      List<? extends Collection<?>> pPartitionedFormulas,
      int[] pStartOfSubTree);

  List<BooleanFormula> getFormulaTreeInterpolants(
      BooleanFormula pFormula,
      List<? extends Collection<?>> pPartitionedFormulas,
      int[] pStartOfSubTree);

  Integer storeFormulaMaximize(BooleanFormula pFormula, Integer max, Formula pObjective);

  Integer getFormulaMaximize(BooleanFormula pFormula, Formula pObjective);

  Integer storeFormulaMinimize(BooleanFormula pFormula, Integer min, Formula pObjective);

  Integer getFormulaMinimize(BooleanFormula pFormula, Formula pObjective);

  Optional<Rational> storeFormulaUpper(
      BooleanFormula pFormula,
      Optional<Rational> pUpper,
      int pHandle,
      Rational pEpsilon);

  Optional<Rational>
      getFormulaUpper(BooleanFormula pFormula, int pHandle, Rational pEpsilon);

  Optional<Rational> storeFormulaLower(
      BooleanFormula pFormula,
      Optional<Rational> pLower,
      int pHandle,
      Rational pEpsilon);

  Optional<Rational>
      getFormulaLower(BooleanFormula pFormula, int pHandle, Rational pEpsilon);

  void close();
}
