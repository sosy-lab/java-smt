// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;

public class CVC5ArrayFormulaManager extends AbstractArrayFormulaManager<Term, Sort, Solver, Term> {

  private final Solver solver;

  public CVC5ArrayFormulaManager(CVC5FormulaCreator pFormulaCreator) {
    super(pFormulaCreator);
    solver = pFormulaCreator.getEnv();
  }

  @Override
  protected Term select(Term pArray, Term pIndex) {
    return solver.mkTerm(Kind.SELECT, pArray, pIndex);
  }

  @Override
  protected Term store(Term pArray, Term pIndex, Term pValue) {
    return solver.mkTerm(Kind.STORE, pArray, pIndex, pValue);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> Term internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    final ArrayFormulaType<TI, TE> arrayFormulaType =
        FormulaType.getArrayType(pIndexType, pElementType);
    final Sort cvc5ArrayType = toSolverType(arrayFormulaType);
    return getFormulaCreator().makeVariable(cvc5ArrayType, pName);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Term internalMakeArray(
      Term elseElem, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    final ArrayFormulaType<TI, TE> arrayFormulaType =
        FormulaType.getArrayType(pIndexType, pElementType);
    final Sort cvc5ArrayType = toSolverType(arrayFormulaType);
    return solver.mkConstArray(cvc5ArrayType, elseElem);
  }

  @Override
  protected Term equivalence(Term pArray1, Term pArray2) {
    return solver.mkTerm(Kind.EQUAL, pArray1, pArray2);
  }
}
