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
package org.sosy_lab.java_smt.solvers.wrapper.strategy;

import com.google.errorprone.annotations.Immutable;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingFormula;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingFormulaStore;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingVariable;

@Immutable
public class RenamingStrategy implements CanonizingStrategy {

  @Override
  public CanonizingFormula
      canonizeVariable(
          FormulaManager pMgr,
          String pName,
          FormulaType<?> pType,
          CanonizingFormulaStore pCaller) {
    String canonizedName = canonizeVariableName(pName, pCaller);

    return new CanonizingVariable(pMgr, canonizedName, pType);
  }

  private static String canonizeVariableName(String pName, CanonizingFormulaStore pCaller) {
    return pCaller.mapName(pName);
  }
}
