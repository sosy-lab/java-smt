/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.wrapper.canonizing;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.solvers.wrapper.strategy.CanonizingStrategy;

public class CanonizingFormulaStore {

  private Set<CanonizingFormula> constraints;
  private Set<CanonizingFormula> canonizedConstraints;

  private final Map<CanonizingFormula, CanonizingFormula> memoizedFormulas = new HashMap<>();
  private final Map<String, String> nameMap = new HashMap<>();

  private CanonizingFormula currentConstraint;
  private FormulaType<?> nextLiteralsType;

  private FormulaManager mgr;

  private List<CanonizingStrategy> strategies;
  private String nameSchema = "v_";
  // FIXME: probably AtomicInteger/IntegerCounterProvider/IntegerIdGenerator (?)
  private int nameCounter = 0;

  public CanonizingFormulaStore(FormulaManager pMgr, List<CanonizingStrategy> pStrategies) {
    this(pMgr, null, null, null, null, pStrategies);
  }

  public CanonizingFormulaStore(
      FormulaManager pMgr,
      CanonizingFormula pFormula,
      FormulaType<?> pType,
      Set<CanonizingFormula> pConstraints,
      Set<CanonizingFormula> pCanonizedConstraints,
      List<CanonizingStrategy> pStrategies) {
    mgr = pMgr;
    currentConstraint = pFormula;
    nextLiteralsType = pType;
    constraints = pConstraints;
    canonizedConstraints = pCanonizedConstraints;
    strategies = pStrategies;
  }

  public CanonizingFormulaStore copy() {
    CanonizingFormula constraint = currentConstraint != null ? currentConstraint.copy() : null;
    return new CanonizingFormulaStore(
        mgr,
        constraint,
        nextLiteralsType,
        constraints,
        canonizedConstraints,
        strategies);
  }

  public BooleanFormula getFormula() {
    // FIXME: at this point only BooleanFormula may be returned, but that should somehow still be
    // checked
    return (BooleanFormula) currentConstraint.toFormula(mgr);
  }

  private void canonize() {
    canonizedConstraints = new HashSet<>();
    safetyCheckForConstantConstraints();

    for (CanonizingFormula cF : constraints) {
      CanonizingFormula canonizedF = cF;
      for (CanonizingStrategy strategy : strategies) {
        canonizedF = canonizedF.canonize(strategy, this);
      }
      canonizedConstraints.add(canonizedF);
    }
  }

  private void safetyCheckForConstantConstraints() {
    // XXX: in case of single boolean-constant-constraints that situation can happen
    if (currentConstraint != null) {
      if (constraints == null) {
        constraints = new HashSet<>();
      }
      if (!constraints.contains(currentConstraint)) {
        constraints.add(currentConstraint);
      }
    }
  }

  public CanonizingFormula getSomeCanonizedFormula() {
    canonize();
    for (CanonizingFormula cf : canonizedConstraints) {
      return cf;
    }
    return null;
  }

  public BooleanFormula getCanonizedFormula() {
    canonize();
    return toFormula(mgr, canonizedConstraints);
  }

  private BooleanFormula toFormula(
      FormulaManager pMgr, Set<CanonizingFormula> pCanonizedConstraints) {
    BooleanFormula result = null;
    for (CanonizingFormula cF : pCanonizedConstraints) {
      if (result == null) {
        result = (BooleanFormula) cF.toFormula(pMgr);
      } else {
        result = pMgr.getBooleanFormulaManager().and(result, (BooleanFormula) cF.toFormula(pMgr));
      }
    }
    return result;
  }

  public CanonizingFormula getSomeConstraint() {
    safetyCheckForConstantConstraints();
    for (CanonizingFormula cF : constraints) {
      return cF;
    }
    return null;
  }

  public void push() {
    // TODO implement
  }

  public void pop() {
    // TODO implement
  }

  public void storeOperator(CanonizingFormula pOp) {
    currentConstraint = pOp;
  }

  public void storeType(FormulaType<?> pFormulaType) {
    nextLiteralsType = pFormulaType;
  }

  public void closeOperand(CanonizingFormula pFormula) {
    if (currentConstraint != null) {
      if (currentConstraint.equals(pFormula)) {
        addConstraint(currentConstraint);
      }
    } else {
      assert false;
    }
  }

  private void addConstraint(CanonizingFormula pConstraint) {
    if (constraints == null) {
      constraints = new HashSet<>();
    }

    constraints.add(pConstraint);
  }

  public FormulaType<?> popType() {
    FormulaType<?> pop = nextLiteralsType;
    nextLiteralsType = null;
    return pop;
  }

  public CanonizingFormula remember(CanonizingFormula pCanonizingFormula) {
    memoizedFormulas.putIfAbsent(pCanonizingFormula, pCanonizingFormula);
    CanonizingFormula result = memoizedFormulas.get(pCanonizingFormula);
    currentConstraint = result;
    if (result instanceof CanonizingVariable) {
      ((CanonizingVariable) result).incrementCount();
    }
    return result;
  }

  public String mapName(String pOriginalName) {
    String mappedName = checkName(pOriginalName);
    if (mappedName.equals(pOriginalName)) {
      mappedName = nameSchema + nameCounter++;
      nameMap.put(pOriginalName, mappedName);
    }
    return mappedName;
  }

  private String checkName(String pName) {
    if (nameMap.containsKey(pName)) {
      return nameMap.get(pName);
    }
    return pName;
  }
}
