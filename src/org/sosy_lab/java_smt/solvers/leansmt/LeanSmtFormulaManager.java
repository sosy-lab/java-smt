// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

final class LeanSmtFormulaManager
    extends AbstractFormulaManager<Long, LeanSmtType, Long, LeanSmtFunctionDecl> {

  LeanSmtFormulaManager(
      LeanSmtFormulaCreator pFormulaCreator,
      LeanSmtUFManager pFunctionManager,
      LeanSmtBooleanFormulaManager pBooleanManager,
      LeanSmtIntegerFormulaManager pIntegerManager,
      LeanSmtRationalFormulaManager pRationalManager,
      LeanSmtBitvectorFormulaManager pBitvectorManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitvectorManager,
        null,
        null,
        null,
        null,
        null,
        null);
  }

  private LeanSmtFormulaCreator creator() {
    return (LeanSmtFormulaCreator) getFormulaCreator();
  }

  @Override
  protected Long equalImpl(Long pArg1, Long pArg2) {
    return creator()
        .makeBinary(
            "=",
            org.sosy_lab.java_smt.api.FunctionDeclarationKind.EQ,
            FormulaType.BooleanType,
            pArg1,
            pArg2);
  }

  @Override
  protected Long distinctImpl(Collection<Long> pArgs) {
    if (pArgs.size() < 2) {
      return creator().getTrueHandle();
    }
    List<Long> args = new ArrayList<>(pArgs);
    Long result = null;
    for (int i = 0; i < args.size(); i++) {
      for (int j = i + 1; j < args.size(); j++) {
        Long neq =
            creator()
                .makeBinary(
                    "distinct",
                    org.sosy_lab.java_smt.api.FunctionDeclarationKind.DISTINCT,
                    FormulaType.BooleanType,
                    args.get(i),
                    args.get(j));
        if (result == null) {
          result = neq;
        } else {
          result =
              creator()
                  .makeBinary(
                      "and",
                      org.sosy_lab.java_smt.api.FunctionDeclarationKind.AND,
                      FormulaType.BooleanType,
                      result,
                      neq);
        }
      }
    }
    return result == null ? creator().getTrueHandle() : result;
  }

  @Override
  public Long parseImpl(String pS) throws IllegalArgumentException {
    throw new UnsupportedOperationException("LeanSMT backend does not support parsing formulae");
  }

  @Override
  public String dumpFormulaImpl(Long pFormula) throws IOException {
    return new LeanSmtSmtLibPrinter(creator()).dumpFormula(pFormula);
  }
}
