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

import com.google.common.primitives.Longs;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BoolectorQuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Long, Long, BoolectorEnvironment, Long> {

  private final long btor;
  private static Map<Long, Long[]> quantifierMap = new HashMap<>();

  BoolectorQuantifiedFormulaManager(FormulaCreator<Long, Long, BoolectorEnvironment, Long>
          pCreator) {
    super(pCreator);
    btor = getFormulaCreator().getEnv().getBtor();
  }

  @Override
  protected Long eliminateQuantifiers(Long pExtractInfo)
      throws SolverException, InterruptedException {
    // TODO SAT or simplify?
    return null;
  }

  @Override
  public Long mkQuantifier(Quantifier pQ, List<Long> pVars, Long pBody) {
    Long Newquantifier = null;
    if (pVars.size() == 0) {
      throw new IllegalArgumentException("List of quantified variables can not be empty");
    }
    long[] varsArray = Longs.toArray(pVars);
    for (long param : varsArray) {
      if (!BtorJNI.boolector_is_param(btor, param)) {
        throw new IllegalArgumentException("pVariables need to be parameter nodes in boolector.");
      }
    }
    // We need the body and variables later and boolector does not give them back!
    Long[] bodyPlusList = new Long[pVars.size() + 2];
    if (pQ == Quantifier.FORALL) {
      Newquantifier = BtorJNI.boolector_forall(btor, varsArray, varsArray.length, pBody);
      bodyPlusList[1] = (long) 0;
    } else {
      Newquantifier = BtorJNI.boolector_exists(btor, varsArray, varsArray.length, pBody);
      bodyPlusList[0] = (long) 1;
    }
    bodyPlusList[1] = pBody;
    for (int i = 2; i < pVars.size() + 2; i++) {
      bodyPlusList[i] = pVars.get(i - 2);
    }
    quantifierMap.put(Newquantifier, bodyPlusList);
    return Newquantifier;
  }

  /**
   * Gives back the variables and body of an Quantifier (forall and exists). Since Boolector cant
   * give back the used variables or the body of an Quantifier we have to save and return them
   * manually.
   *
   * @param key Boolector Node (Formula) you want.
   * @return Long Array, first item indicates type(0 = forall, 1 = exists), second item is
   *         Quantifier Body, rest is variables. Null if there is no entry.
   */
  protected static Long[] getQuantVars(Long key) {
    if (quantifierMap.containsKey(key)) {
      return quantifierMap.get(key);
    }
    return null;
  }

}
