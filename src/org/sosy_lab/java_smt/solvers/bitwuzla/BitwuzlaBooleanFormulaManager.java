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

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BitwuzlaBooleanFormulaManager extends AbstractBooleanFormulaManager<Long, Long, Long
    , Long> {
  private final long bitwuzla;
  private final long pTrue;
  private final long pFalse;
  protected BitwuzlaBooleanFormulaManager(FormulaCreator<Long, Long, Long, Long> pCreator) {
    super(pCreator);
    bitwuzla = getFormulaCreator().getEnv();
    pTrue = bitwuzlaJNI.bitwuzla_mk_true(bitwuzla);
    pFalse = bitwuzlaJNI.bitwuzla_mk_false(bitwuzla);
  }

  @Override
  protected Long makeVariableImpl(String pVar) {
    long boolType = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(boolType, pVar);
  }

  @Override
  protected Long makeBooleanImpl(boolean value) {
    return value ? pTrue : pFalse;
  }

  @Override
  protected Long not(Long pParam1) {
    return bitwuzlaJNI.bitwuzla_mk_term1(bitwuzla, SWIG_BitwuzlaKind.BITWUZLA_KIND_NOT.swigValue(), pParam1);
  }

  @Override
  protected Long and(Long pParam1, Long pParam2) {
    return bitwuzlaJNI.bitwuzla_mk_term2(bitwuzla,
        SWIG_BitwuzlaKind.BITWUZLA_KIND_AND.swigValue(), pParam1, pParam2);

  }

  @Override
  protected Long or(Long pParam1, Long pParam2) {
    return bitwuzlaJNI.bitwuzla_mk_term2(bitwuzla,
        SWIG_BitwuzlaKind.BITWUZLA_KIND_OR.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long xor(Long pParam1, Long pParam2) {
    return bitwuzlaJNI.bitwuzla_mk_term2(bitwuzla,
        SWIG_BitwuzlaKind.BITWUZLA_KIND_XOR.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long equivalence(Long bits1, Long bits2) {
    return bitwuzlaJNI.bitwuzla_mk_term2(bitwuzla,
        SWIG_BitwuzlaKind.BITWUZLA_KIND_IFF.swigValue(), bits1, bits2);
  }

  @Override
  protected boolean isTrue(Long bits) {
    return false;
  }

  @Override
  protected boolean isFalse(Long bits) {
    return false;
  }

  @Override
  protected Long ifThenElse(Long cond, Long f1, Long f2) {
    return bitwuzlaJNI.bitwuzla_mk_term2(bitwuzla,
        SWIG_BitwuzlaKind.BITWUZLA_KIND_ITE.swigValue(), f1, f2);
  }
}
