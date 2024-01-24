// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BitwuzlaBooleanFormulaManager
    extends AbstractBooleanFormulaManager<Long, Long, Long, BitwuzlaDeclaration> {
  // private final long bitwuzla;
  private final long pTrue;
  private final long pFalse;

  protected BitwuzlaBooleanFormulaManager(
      FormulaCreator<Long, Long, Long, BitwuzlaDeclaration> pCreator) {
    super(pCreator);
    // bitwuzla = getFormulaCreator().getEnv();
    pTrue = BitwuzlaJNI.bitwuzla_mk_true();
    pFalse = BitwuzlaJNI.bitwuzla_mk_false();
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
    if (isTrue(pParam1)) {
      return pFalse;
    } else if (isFalse(pParam1)) {
      return pTrue;
    }

    if (BitwuzlaJNI.bitwuzla_term_get_kind(pParam1) == BitwuzlaKind.BITWUZLA_KIND_NOT.swigValue()) {
      long[] size = new long[1];
      long[] pChildren = BitwuzlaJNI.bitwuzla_term_get_children(pParam1, size);
      return pChildren[0];
    }
    return BitwuzlaJNI.bitwuzla_mk_term1(BitwuzlaKind.BITWUZLA_KIND_NOT.swigValue(), pParam1);
  }

  @Override
  protected Long and(Long pParam1, Long pParam2) {
    if (isTrue(pParam1)) {
      return pParam2;
    } else if (isTrue(pParam2)) {
      return pParam1;
    } else if (isFalse(pParam1)) {
      return pFalse;
    } else if (isFalse(pParam2)) {
      return pFalse;
    } else if (pParam1.equals(pParam2)) {
      return pParam1;
    }
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_AND.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long or(Long pParam1, Long pParam2) {
    if (isTrue(pParam1)) {
      return pTrue;
    } else if (isTrue(pParam2)) {
      return pTrue;
    } else if (isFalse(pParam1)) {
      return pParam2;
    } else if (isFalse(pParam2)) {
      return pParam1;
    } else if (pParam1.equals(pParam2)) {
      return pParam1;
    }
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_OR.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long xor(Long pParam1, Long pParam2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(
        BitwuzlaKind.BITWUZLA_KIND_XOR.swigValue(), pParam1, pParam2);
  }

  @Override
  protected Long equivalence(Long bits1, Long bits2) {
    return BitwuzlaJNI.bitwuzla_mk_term2(BitwuzlaKind.BITWUZLA_KIND_IFF.swigValue(), bits1, bits2);
  }

  @Override
  protected boolean isTrue(Long bits) {
    return BitwuzlaJNI.bitwuzla_term_is_true(bits);
  }

  @Override
  protected boolean isFalse(Long bits) {
    return BitwuzlaJNI.bitwuzla_term_is_false(bits);
  }

  @Override
  protected Long ifThenElse(Long pCond, Long pF1, Long pF2) {
    if (isTrue(pCond)) {
      return pF1;
    } else if (isFalse(pCond)) {
      return pF2;
    } else if (pF1.equals(pF2)) {
      return pF1;
    } else if (isTrue(pF1) && isFalse(pF2)) {
      return pCond;
    } else if (isFalse(pF1) && isTrue(pF2)) {
      return not(pCond);
    }
    return BitwuzlaJNI.bitwuzla_mk_term3(
        BitwuzlaKind.BITWUZLA_KIND_ITE.swigValue(), pCond, pF1, pF2);
  }
}
