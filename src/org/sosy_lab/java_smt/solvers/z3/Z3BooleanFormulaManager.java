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
package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.primitives.Longs;
import com.microsoft.z3.Native;
import java.util.Collection;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

class Z3BooleanFormulaManager extends AbstractBooleanFormulaManager<Long, Long, Long, Long> {

  private final long z3context;
  private final long z3true;
  private final long z3false;

  Z3BooleanFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    z3context = creator.getEnv();
    z3true = Native.mkTrue(z3context);
    Native.incRef(z3context, z3true);
    z3false = Native.mkFalse(z3context);
    Native.incRef(z3context, z3false);
  }

  @Override
  protected Long makeVariableImpl(String varName) {
    long type = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Long makeBooleanImpl(boolean pValue) {
    if (pValue) {
      return Native.mkTrue(z3context);
    } else {
      return Native.mkFalse(z3context);
    }
  }

  @Override
  protected Long not(Long pParam) {
    return Native.mkNot(z3context, pParam);
  }

  @Override
  protected Long and(Long pParam1, Long pParam2) {
    if (isTrue(pParam1)) {
      return pParam2;
    } else if (isTrue(pParam2)) {
      return pParam1;
    } else if (isFalse(pParam1)) {
      return z3false;
    } else if (isFalse(pParam2)) {
      return z3false;
    } else if (Native.isEqAst(z3context, pParam1, pParam2)) {
      return pParam1;
    }
    return Native.mkAnd(z3context, 2, new long[] {pParam1, pParam2});
  }

  @Override
  protected Long or(Long pParam1, Long pParam2) {
    if (isTrue(pParam1)) {
      return z3true;
    } else if (isTrue(pParam2)) {
      return z3true;
    } else if (isFalse(pParam1)) {
      return pParam2;
    } else if (isFalse(pParam2)) {
      return pParam1;
    } else if (Native.isEqAst(z3context, pParam1, pParam2)) {
      return pParam1;
    }
    return Native.mkOr(z3context, 2, new long[] {pParam1, pParam2});
  }

  @Override
  protected Long orImpl(Collection<Long> params) {
    return Native.mkOr(z3context, params.size(), Longs.toArray(params));
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toDisjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::or);
  }

  @Override
  protected Long andImpl(Collection<Long> params) {
    return Native.mkAnd(z3context, params.size(), Longs.toArray(params));
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toConjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::and);
  }

  @Override
  protected Long xor(Long pParam1, Long pParam2) {
    return Native.mkXor(z3context, pParam1, pParam2);
  }

  @Override
  protected Long equivalence(Long pBits1, Long pBits2) {
    return Native.mkEq(z3context, pBits1, pBits2);
  }

  @Override
  protected Long implication(Long pBits1, Long pBits2) {
    return Native.mkImplies(z3context, pBits1, pBits2);
  }

  @Override
  protected boolean isTrue(Long pParam) {
    return Native.isEqAst(z3context, pParam, z3true);
  }

  @Override
  protected boolean isFalse(Long pParam) {
    return Native.isEqAst(z3context, pParam, z3false);
  }

  @Override
  protected Long ifThenElse(Long pCond, Long pF1, Long pF2) {
    return Native.mkIte(z3context, pCond, pF1, pF2);
  }
}
