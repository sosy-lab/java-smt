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
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_exists;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_forall;

import com.google.common.primitives.Ints;
import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class Yices2QuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Integer, Integer, Long, Integer> {

  protected Yices2QuantifiedFormulaManager(
      FormulaCreator<Integer, Integer, Long, Integer> pCreator) {
    super(pCreator);
    // TODO Auto-generated constructor stub
  }

  @Override
  protected Integer eliminateQuantifiers(Integer pExtractInfo)
      throws SolverException, InterruptedException {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException("Yices does not support eliminating Quantifiers.");
  }

  @Override
  public Integer mkQuantifier(Quantifier pQ, List<Integer> pVars, Integer pBody) {
    // TODO Auto-generated method stub
    if (pVars.isEmpty()) {
      throw new IllegalArgumentException("Empty variable list for Quantifier.");
    } else {
      int[] terms = Ints.toArray(pVars);
      if (pQ == Quantifier.FORALL) {
        return yices_forall(terms.length, terms, pBody);
      } else if (pQ == Quantifier.EXISTS) {
        return yices_exists(terms.length, terms, pBody);
      }
    }
    return null;
  }
}
