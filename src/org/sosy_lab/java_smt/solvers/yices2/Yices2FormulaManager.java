/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
 *  All rights reserved.
 *
 *  SPDX-License-Identifier: Apache-2.0 AND GPL-3.0-or-later
 */
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_APP_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_child;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_constructor;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_children;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_num_children;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_of_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_to_string;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import java.io.IOException;
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

public class Yices2FormulaManager extends AbstractFormulaManager<Integer, Integer, Long, Integer> {

  protected Yices2FormulaManager(
      Yices2FormulaCreator pFormulaCreator,
      Yices2UFManager pFunctionManager,
      Yices2BooleanFormulaManager pBooleanManager,
      Yices2IntegerFormulaManager pIntegerManager,
      Yices2RationalFormulaManager pRationalManager,
      Yices2BitvectorFormulaManager pBitvectorManager) {
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
        null);
  }

  static Integer getYicesTerm(Formula pT) {
    return ((Yices2Formula) pT).getTerm();
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    // TODO Might expect Yices input language instead of smt-lib2 notation
    return getFormulaCreator().encapsulateBoolean(yices_parse_term(pS));
  }

  @Override
  public Appender dumpFormula(final Integer formula) {
    assert getFormulaCreator().getFormulaType(formula) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";
    return new Appenders.AbstractAppender() {

      @Override
      public void appendTo(Appendable out) throws IOException {
        Map<String, Formula> varsAndUFs =
            extractVariablesAndUFs(getFormulaCreator().encapsulateWithTypeOf(formula));
        for (Map.Entry<String, Formula> entry : varsAndUFs.entrySet()) {
          final int term = ((Yices2Formula) entry.getValue()).getTerm();
          final int type;
          if (yices_term_constructor(term) == YICES_APP_TERM) {
            // Is an UF. Correct type is carried by first child.
            type = yices_type_of_term(yices_term_child(term, 0));
          } else {
            type = yices_type_of_term(term);
          }
          final int[] types;
          if (yices_type_num_children(type) == 0) {
            types = new int[] {type};
          } else {
            types = yices_type_children(type); // adds children types and then return type
          }
          if (types.length > 0) {
            out.append("(declare-fun ");
            out.append(PrintTerm.quoteIdentifier(entry.getKey()));
            out.append(" (");
            for (int i = 0; i < types.length - 1; i++) {
              out.append(getTypeRepr(types[i]));
              if (i + 1 < types.length - 1) {
                out.append(' ');
              }
            }
            out.append(") ");
            out.append(getTypeRepr(types[types.length - 1]));
            out.append(")\n");
          }
        }
        // TODO fold formula to avoid exp. overhead
        out.append("(assert " + yices_term_to_string(formula) + ")");
      }

      private String getTypeRepr(int type) {
        String typeRepr = yices_type_to_string(type);
        return typeRepr.substring(0, 1).toUpperCase() + typeRepr.substring(1);
      }
    };
  }
}
