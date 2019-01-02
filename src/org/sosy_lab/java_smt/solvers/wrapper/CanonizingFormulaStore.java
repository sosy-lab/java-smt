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
package org.sosy_lab.java_smt.solvers.wrapper;

import java.util.HashSet;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;

public class CanonizingFormulaStore {

  private Set<CanonizingFormula> constraints;
  private Set<CanonizingFormula> canonizedConstraints;

  private CanonizingFormula currentConstraint;
  private FormulaType<?> nextLiteralsType;

  private FormulaManager mgr;

  public CanonizingFormulaStore(FormulaManager pMgr) {
    this(pMgr, null, null, null, null);
  }

  public CanonizingFormulaStore(
      FormulaManager pMgr,
      CanonizingFormula pFormula,
      FormulaType<?> pType,
      Set<CanonizingFormula> pConstraints,
      Set<CanonizingFormula> pCanonizedConstraints) {
    mgr = pMgr;
    currentConstraint = pFormula;
    nextLiteralsType = pType;
    constraints = pConstraints;
    canonizedConstraints = pCanonizedConstraints;
  }

  public CanonizingFormulaStore copy() {
    CanonizingFormula constraint = currentConstraint != null ? currentConstraint.copy() : null;
    return new CanonizingFormulaStore(
        mgr, constraint, nextLiteralsType, constraints, canonizedConstraints);
  }

  public BooleanFormula getFormula() {
    // FIXME: at this point only BooleanFormula may be returned, but that should somehow still be
    // checked
    return (BooleanFormula) currentConstraint.toFormula(mgr);
  }

  private void canonize() {
    canonizedConstraints = new HashSet<>();
    for (CanonizingFormula cF : constraints) {
      canonizedConstraints.add(cF.canonize());
    }
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
    if (currentConstraint == null) {
      currentConstraint = pOp;
    }
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
}
