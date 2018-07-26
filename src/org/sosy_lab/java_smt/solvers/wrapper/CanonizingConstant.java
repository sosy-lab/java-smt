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

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;

public class CanonizingConstant implements CanonizingFormula {

  private FormulaManager mgr;
  private Object value;
  private FormulaType<?> type;

  private CanonizingFormula parent;

  public CanonizingConstant(FormulaManager pMgr, Object pValue, FormulaType<?> pType) {
    mgr = pMgr;
    value = pValue;
    type = pType;
  }

  @Override
  public void add(CanonizingFormula pFormula) {
    assert false;
  }

  @Override
  public void setParent(CanonizingFormula pFormula) {
    parent = pFormula;
  }

  @Override
  public CanonizingFormula getParent() {
    return parent;
  }

  public Object getValue() {
    return value;
  }

  public FormulaType<?> getType() {
    return type;
  }

  @Override
  public CanonizingFormula copy() {
    CanonizingFormula copy = new CanonizingConstant(mgr, value, type);

    return copy;
  }

  @Override
  public BooleanFormula toFormula(FormulaManager pMgr) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public CanonizingFormula canonize() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public FormulaManager getFormulaManager() {
    return mgr;
  }

  @Override
  public void toString(StringBuilder pBuilder) {
    pBuilder.append(value);
  }

  @Override
  public String toString() {
    return value.toString();
  }
}
