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

package org.sosy_lab.java_smt.solvers.bitwuzla;

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BitwuzlaArrayFormulaManager extends
                                         AbstractArrayFormulaManager<Long, Long, Long, Long> {
  protected BitwuzlaArrayFormulaManager(FormulaCreator<Long, Long, Long, Long> pFormulaCreator) {
    super(pFormulaCreator);
  }

  @Override
  protected Long select(Long pArray, Long pIndex) {
    return null;
  }

  @Override
  protected Long store(Long pArray, Long pIndex, Long pValue) {
    return null;
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Long internalMakeArray(
      String pName,
      FormulaType<TI> pIndexType,
      FormulaType<TE> pElementType) {
    return null;
  }

  @Override
  protected Long equivalence(Long pArray1, Long pArray2) {
    return null;
  }
}
