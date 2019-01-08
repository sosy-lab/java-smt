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

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.solvers.wrapper.strategy.CanonizingStrategy;

public class CanonizingVariable implements CanonizingFormula {

  private FormulaManager mgr;
  private String name;
  private FormulaType<?> type;

  public CanonizingVariable(FormulaManager pMgr, String pName, FormulaType<?> pType) {
    mgr = pMgr;
    name = pName;
    type = pType;
  }

  public String getName() {
    return name;
  }

  public FormulaType<?> getType() {
    return type;
  }

  @Override
  public CanonizingFormula copy() {
    CanonizingFormula copy = new CanonizingVariable(mgr, name, type);

    return copy;
  }

  @Override
  public Formula toFormula(FormulaManager pMgr) {
    return pMgr.makeVariable(type, name);
  }

  @Override
  public CanonizingFormula canonize(CanonizingStrategy pStrategy) {
    return pStrategy.canonizeVariable(mgr, name, type);
  }

  @Override
  public FormulaManager getFormulaManager() {
    return mgr;
  }

  @Override
  public String toString() {
    return name;
  }

  @Override
  public void toString(StringBuilder pBuilder) {
    pBuilder.append(name);
  }
}
