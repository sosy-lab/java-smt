// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Kind;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.TermManager;

public class BitwuzlaArrayFormulaManager
    extends AbstractArrayFormulaManager<Term, Sort, Void, BitwuzlaDeclaration> {
  private final TermManager termManager;

  protected BitwuzlaArrayFormulaManager(BitwuzlaFormulaCreator pCreator) {
    super(pCreator);
    termManager = pCreator.getTermManager();
  }

  @Override
  protected Term select(Term pArray, Term pIndex) {
    return termManager.mk_term(Kind.ARRAY_SELECT, pArray, pIndex);
  }

  @Override
  protected Term store(Term pArray, Term pIndex, Term pValue) {
    return termManager.mk_term(Kind.ARRAY_STORE, pArray, pIndex, pValue);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> Term internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    final ArrayFormulaType<TI, TE> arrayFormulaType =
        FormulaType.getArrayType(pIndexType, pElementType);
    final Sort bitwuzlaArrayType = toSolverType(arrayFormulaType);
    Term newVar = getFormulaCreator().makeVariable(bitwuzlaArrayType, pName);
    return newVar;
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Term internalMakeArray(
      FormulaType<TI> pIndexType,
      FormulaType<TE> pElementType,
      Term elseElem) {
    final ArrayFormulaType<TI, TE> arrayFormulaType =
        FormulaType.getArrayType(pIndexType, pElementType);
    final Sort bitwuzlaArrayType = toSolverType(arrayFormulaType);
    return termManager.mk_const_array(bitwuzlaArrayType, elseElem);
  }

  @Override
  protected Term equivalence(Term pArray1, Term pArray2) {
    return termManager.mk_term(Kind.EQUAL, pArray1, pArray2);
  }
}
