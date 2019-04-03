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
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;

public interface SMTCache {

  /** FIXME: For Allsat some strategy has yet to be thought of, to handle the generic callback. */
  enum CachingMode {
    IN_MEMORY,
    SIMPLE_BINARY;
  }

  static SMTCache newSMTCache(CachingMode pMode, Configuration config)
      throws InvalidConfigurationException {
    SMTCache cache = null;

    switch (pMode) {
      case IN_MEMORY:
        cache = new InMemorySMTCache();
        break;
      case SIMPLE_BINARY:
        cache = new SimpleBinarySMTCache(config);
        break;
      default:
        // no-op. just return null
    }

    return cache;
  }

  Boolean storeFormulaUnsat(Formula pFormula, boolean pUnsat);

  Boolean isFormulaUnsat(Formula pFormula);

  Boolean storeFormulaUnsatWithAssumptions(
      Formula pFormula, boolean pUnsat, Collection<Formula> pAssumptions);

  Boolean isFormulaUnsatWithAssumptions(Formula pFormula, Collection<Formula> pAssumptions);

  Model storeFormulaModel(Formula pFormula, Model pModel);

  Model getFormulaModel(Formula pFormula);

  ImmutableList<ValueAssignment> storeFormulaModelAssignments(
      Formula pFormula, ImmutableList<ValueAssignment> pAssignments);

  ImmutableList<ValueAssignment> getFormulaModelAssignments(Formula pFormula);

  List<Formula> storeFormulaUnsatCore(Formula pFormula, List<Formula> pUnsatCore);

  List<Formula> getFormulaUnsatCore(Formula pFormula);

  Optional<List<Formula>> storeFormulaUnsatCoreOverAssumptions(
      Formula pFormula, Optional<List<Formula>> pUnsatCore, Collection<Formula> pAssumptions);

  Optional<List<Formula>> getFormulaUnsatCoreOverAssumptions(
      Formula pFormula, Collection<Formula> pAssumptions);

  Formula storeFormulaInterpolant(
      Formula pFormula, Formula pInterpolant, Collection<?> pFormulasOfA);

  Formula getFormulaInterpolant(Formula pFormula, Collection<?> pFormulasOfA);

  List<Formula> storeFormulaTreeInterpolants(
      Formula pFormula,
      List<Formula> pTreeInterpolants,
      List<? extends Collection<?>> pPartitionedFormulas,
      int[] pStartOfSubTree);

  List<Formula> getFormulaTreeInterpolants(
      Formula pFormula, List<? extends Collection<?>> pPartitionedFormulas, int[] pStartOfSubTree);

  Integer storeFormulaMaximize(Formula pFormula, Integer max, Formula pObjective);

  Integer getFormulaMaximize(Formula pFormula, Formula pObjective);

  Integer storeFormulaMinimize(Formula pFormula, Integer min, Formula pObjective);

  Integer getFormulaMinimize(Formula pFormula, Formula pObjective);

  Optional<Rational> storeFormulaUpper(
      Formula pFormula, Optional<Rational> pUpper, int pHandle, Rational pEpsilon);

  Optional<Rational> getFormulaUpper(Formula pFormula, int pHandle, Rational pEpsilon);

  Optional<Rational> storeFormulaLower(
      Formula pFormula, Optional<Rational> pLower, int pHandle, Rational pEpsilon);

  Optional<Rational> getFormulaLower(Formula pFormula, int pHandle, Rational pEpsilon);

  void close();

  List<List<Formula>> storeAllSat(
      Formula pFormula, List<Formula> pImportant, List<List<Formula>> pCached);

  List<List<Formula>> getAllSat(Formula pFormula, List<Formula> pImportant);
}
