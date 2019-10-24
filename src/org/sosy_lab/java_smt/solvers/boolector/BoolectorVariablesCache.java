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
package org.sosy_lab.java_smt.solvers.boolector;

import java.util.LinkedHashMap;
import java.util.Map;
import javax.annotation.Nullable;

/**
 * Boolector does not have an internal variables cache. Thus we need to check for existing symbols
 * on our own. This utility class is a wrapper around some caches.
 */
public class BoolectorVariablesCache {

  /** Mapping of unique Boolector name(key) to JavaSMT name(value) */
  private final Map<String, String> newNameNameMap = new LinkedHashMap<>();

  /** Mapping unique Boolector name(key) to formula(value) */
  private final Map<String, Long> nameFormulaCacheMap = new LinkedHashMap<>();

  private long btor;

  BoolectorVariablesCache(long btor) {
    this.btor = btor;
  }

  /**
   * Checks whether or not the varName is used and finds a new one.
   *
   * @param javaSMTVarName variable name used in JavaSmt.
   * @return new btor variable name if the input name is already used, the old one else.
   */
  protected String getNewVarName(String javaSMTVarName) {
    String btorVarName = javaSMTVarName;
    int tail = 1;
    while (newNameNameMap.containsKey(btorVarName)) {
      btorVarName = javaSMTVarName + tail;
      tail++;
    }
    return btorVarName;
  }

  /**
   * Checks whether or not there is a formula with that name and type, and gives it back if there
   * is, null otherwise.
   *
   * @param javaSMTVarName Name of the potentially new var in JavaSMT
   * @param formulaSort sort of the new var
   * @return null if there is none in the cache. The complete variable(not sort) else.
   */
  @Nullable
  protected Long getExistingFormula(String javaSMTVarName, long formulaSort) {
    Long formulaFromMap = nameFormulaCacheMap.get(javaSMTVarName);
    if (formulaFromMap != null) {
      long mapFormulaSort = BtorJNI.boolector_get_sort(btor, formulaFromMap);
      if (formulaSort == mapFormulaSort) {
        return formulaFromMap;
      }
    }
    return null;
  }

  /**
   * Gives back the variable name used in JavaSMT from the unique name in Boolector.
   *
   * @param btorVarName unique variable name used in Boolector.
   * @return variable name used in JavaSMT.
   */
  protected String getJavaSMTVarName(String btorVarName) {
    return newNameNameMap.get(btorVarName);
  }

  /**
   * Checks if the name is already in use. Return false if not.
   *
   * @param varName name to be checked
   * @return true if name is already in use, false otherwise.
   */
  protected boolean isNameUsed(String varName) {
    return newNameNameMap.containsKey(varName);
  }

  /**
   * @param btorName unique variable name in Boolector
   * @param javasmtName name in JavaSMT
   * @param formula the formula (long)
   */
  protected void enterNewFormula(String btorName, String javasmtName, Long formula) {
    newNameNameMap.put(btorName, javasmtName);
    nameFormulaCacheMap.put(btorName, formula);
  }
}
