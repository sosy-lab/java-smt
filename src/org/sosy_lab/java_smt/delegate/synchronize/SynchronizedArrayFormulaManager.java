/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
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
package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.SolverContext;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
class SynchronizedArrayFormulaManager implements ArrayFormulaManager {

  private final ArrayFormulaManager delegate;
  private final SolverContext sync;

  SynchronizedArrayFormulaManager(ArrayFormulaManager pDelegate, SolverContext pSync) {
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public <TI extends Formula, TE extends Formula> TE select(
      ArrayFormula<TI, TE> pArray, TI pIndex) {
    synchronized (sync) {
      return delegate.select(pArray, pIndex);
    }
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> store(
      ArrayFormula<TI, TE> pArray, TI pIndex, TE pValue) {
    synchronized (sync) {
      return delegate.store(pArray, pIndex, pValue);
    }
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(String pName, FTI pIndexType, FTE pElementType) {
    synchronized (sync) {
      return delegate.makeArray(pName, pIndexType, pElementType);
    }
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> makeArray(
      String pName, ArrayFormulaType<TI, TE> pType) {
    synchronized (sync) {
      return delegate.makeArray(pName, pType);
    }
  }

  @Override
  public <TI extends Formula, TE extends Formula> BooleanFormula equivalence(
      ArrayFormula<TI, TE> pArray1, ArrayFormula<TI, TE> pArray2) {
    synchronized (sync) {
      return delegate.equivalence(pArray1, pArray2);
    }
  }

  @Override
  public <TI extends Formula> FormulaType<TI> getIndexType(ArrayFormula<TI, ?> pArray) {
    synchronized (sync) {
      return delegate.getIndexType(pArray);
    }
  }

  @Override
  public <TE extends Formula> FormulaType<TE> getElementType(ArrayFormula<?, TE> pArray) {
    synchronized (sync) {
      return delegate.getElementType(pArray);
    }
  }
}
