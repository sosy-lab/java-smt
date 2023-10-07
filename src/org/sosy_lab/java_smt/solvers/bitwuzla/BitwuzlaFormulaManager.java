// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import java.io.IOException;
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

final class BitwuzlaFormulaManager extends AbstractFormulaManager<Long, Long, Long, Long> {

  BitwuzlaFormulaManager(
      BitwuzlaFormulaCreator pFormulaCreator,
      BitwuzlaUFManager pFunctionManager,
      BitwuzlaBooleanFormulaManager pBooleanManager,
      BitwuzlaBitvectorFormulaManager pBitvectorManager,
      BitwuzlaQuantifiedFormulaManager pQuantifierManager,
      BitwuzlaFloatingPointManager pFloatingPointManager,
      BitwuzlaArrayFormulaManager pArrayManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        null,
        null,
        pBitvectorManager,
        pFloatingPointManager,
        pQuantifierManager,
        pArrayManager,
        null,
        null,
        null);
  }

  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    Long term = bitwuzlaJNI.parse(s);
    assert term != null;
    assert bitwuzlaJNI.bitwuzla_term_is_bool(term);
    return super.getFormulaCreator().encapsulateBoolean(term);
  }

  @Override
  public Appender dumpFormula(Long pTerm) {
    assert getFormulaCreator().getFormulaType(pTerm) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";
    return new Appenders.AbstractAppender() {

      @Override
      public void appendTo(Appendable out) throws IOException {
        Map<String, Formula> varsAndUFs =
            extractVariablesAndUFs(getFormulaCreator().encapsulateWithTypeOf(pTerm));
        for (Map.Entry<String, Formula> entry : varsAndUFs.entrySet()) {
          final long currentTerm = ((BitwuzlaFormula) entry.getValue()).getTerm();

          if (bitwuzlaJNI.bitwuzla_term_is_fun(currentTerm)) {
            long[] pDomainSize = new long[1];
            long pArrayDomainTypes =
                bitwuzlaJNI.bitwuzla_term_fun_get_domain_sorts(currentTerm, pDomainSize);
            long numberOfArgs = pDomainSize[0];

            out.append("(declare-fun ");
            out.append(entry.getKey());
            out.append(" (");
            for (int i = 0; i < numberOfArgs; i++) {
              out.append(
                  bitwuzlaJNI.bitwuzla_sort_to_string(
                      bitwuzlaJNI.BitwuzlaSortArray_getitem(pArrayDomainTypes, i)));
              out.append(" ");
            }
            out.append(") ");
            out.append(
                bitwuzlaJNI.bitwuzla_sort_to_string(
                    bitwuzlaJNI.bitwuzla_term_fun_get_codomain_sort(currentTerm)));
            out.append(")\n");
          } else {
            out.append("(declare-const ");
            out.append(entry.getKey());
            out.append(" ");
            out.append(
                bitwuzlaJNI.bitwuzla_sort_to_string(
                    bitwuzlaJNI.bitwuzla_term_get_sort(currentTerm)));
            out.append(")\n");
          }
          out.append("(assert ").append(bitwuzlaJNI.bitwuzla_term_to_string(pTerm)).append(")");
        }
      }
    };
  }

  static long getBitwuzlaTerm(Formula pT) {
    return ((BitwuzlaFormula) pT).getTerm();
  }
}
