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
package org.sosy_lab.java_smt.api;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableMultimap;
import com.google.common.collect.Multimap;

import org.sosy_lab.java_smt.basicimpl.tactics.UfElimination.UninterpretedFunctionApplication;

import java.util.Map;

/**
 * Result of {@link FormulaManager#eliminateUFs(BooleanFormula, UfEliminationResult)}
 */
public class UfEliminationResult {

  private final BooleanFormula formula;
  private final BooleanFormula constraints;
  private final ImmutableMap<Formula, Formula> substitutions;
  private final ImmutableMultimap<FunctionDeclaration<?>, UninterpretedFunctionApplication> ufs;

  public static UfEliminationResult empty(FormulaManager pFormulaManager) {
    BooleanFormula trueFormula = pFormulaManager.getBooleanFormulaManager().makeTrue();
    return new UfEliminationResult(
        trueFormula, trueFormula, ImmutableMap.of(), ImmutableMultimap.of());
  }

  public UfEliminationResult(
      BooleanFormula pFormula,
      BooleanFormula pConstraints,
      ImmutableMap<Formula, Formula> pSubstitutions,
      ImmutableMultimap<FunctionDeclaration<?>, UninterpretedFunctionApplication> pUfs) {
    formula = checkNotNull(pFormula);
    constraints = checkNotNull(pConstraints);
    substitutions = checkNotNull(pSubstitutions);
    ufs = checkNotNull(pUfs);
  }

  /**
   * @return the new {@link Formula} without UFs
   */
  public BooleanFormula getFormula() {
    return formula;
  }

  /**
   * @return the constraints enforcing the functional consistency.
   */
  public BooleanFormula getConstraints() {
    return constraints;
  }

  /**
   * @return the substitution used to replace UFs
   */
  public Map<Formula, Formula> getSubstitution() {
    return substitutions;
  }

  /**
   * @return all eliminated application of Ufs
   */
  public Multimap<FunctionDeclaration<?>, UninterpretedFunctionApplication> getUfs() {
    return ufs;
  }
}
