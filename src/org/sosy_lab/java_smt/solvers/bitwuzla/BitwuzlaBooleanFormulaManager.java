// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Kind;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.TermManager;

public class BitwuzlaBooleanFormulaManager
    extends AbstractBooleanFormulaManager<Term, Sort, Void, BitwuzlaDeclaration> {
  private final TermManager termManager;

  private final Term pTrue;
  private final Term pFalse;

  protected BitwuzlaBooleanFormulaManager(BitwuzlaFormulaCreator pCreator) {
    super(pCreator);
    termManager = pCreator.getTermManager();
    pTrue = termManager.mk_true();
    pFalse = termManager.mk_false();
  }

  @Override
  protected Term makeVariableImpl(String pVar) {
    Sort boolType = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(boolType, pVar);
  }

  @Override
  protected Term makeBooleanImpl(boolean value) {
    return value ? pTrue : pFalse;
  }

  @Override
  protected Term not(Term pParam1) {
    if (isTrue(pParam1)) {
      return pFalse;
    } else if (isFalse(pParam1)) {
      return pTrue;
    }

    if (pParam1.kind() == Kind.NOT) {
      return pParam1.get(0);
    }
    return termManager.mk_term(Kind.NOT, pParam1);
  }

  @Override
  protected Term and(Term pParam1, Term pParam2) {
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
    return termManager.mk_term(Kind.AND, pParam1, pParam2);
  }

  @Override
  protected Term or(Term pParam1, Term pParam2) {
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
    return termManager.mk_term(Kind.OR, pParam1, pParam2);
  }

  @Override
  protected Term xor(Term pParam1, Term pParam2) {
    return termManager.mk_term(Kind.XOR, pParam1, pParam2);
  }

  @Override
  protected Term equivalence(Term bits1, Term bits2) {
    return termManager.mk_term(Kind.IFF, bits1, bits2);
  }

  @Override
  protected boolean isTrue(Term bits) {
    return bits.is_true();
  }

  @Override
  protected boolean isFalse(Term bits) {
    return bits.is_false();
  }

  @Override
  protected Term ifThenElse(Term pCond, Term pF1, Term pF2) {
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
    return termManager.mk_term(Kind.ITE, pCond, pF1, pF2);
  }
}
