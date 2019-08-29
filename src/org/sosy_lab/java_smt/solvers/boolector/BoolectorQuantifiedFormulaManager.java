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
import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BoolectorQuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Long, Long, BoolectorEnvironment, Long> {

  private final long btor;

  BoolectorQuantifiedFormulaManager(FormulaCreator<Long, Long, BoolectorEnvironment, Long>
          pCreator) {
    super(pCreator);
    btor = getFormulaCreator().getEnv().getBtor();
  }

  @Override
  protected Long eliminateQuantifiers(Long pExtractInfo)
      throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Long mkQuantifier(Quantifier pQ, List<Long> pVars, Long pBody) {
    if (pVars.size() == 0) {
      throw new IllegalArgumentException("List of quantified variables can not be empty");
    }
    long[] varsArray = Longs.toArray(pVars);
    for (long param : varsArray) {
      if (!BtorJNI.boolector_is_param(btor, param)) {
        throw new IllegalArgumentException("pVariables need to be parameter nodes in boolector.");
      }
    }
    if (pQ == Quantifier.FORALL) {
      return BtorJNI.boolector_forall(btor, varsArray, varsArray.length, pBody);
    }
    return BtorJNI.boolector_exists(btor, varsArray, varsArray.length, pBody);
  }

}
