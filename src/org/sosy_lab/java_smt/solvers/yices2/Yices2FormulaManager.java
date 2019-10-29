/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
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
        Iterator<Entry<String, Formula>> it = varsAndUFs.entrySet().iterator();
        if (varsAndUFs.isEmpty()) {
          // do nothing, formula is simple bool value
        } else {
          while (it.hasNext()) {
            Map.Entry<String, Formula> entry = it.next();
            Yices2Formula yicesForm = (Yices2Formula) entry.getValue();
            int term = yicesForm.getTerm();
            int type;
            if (yices_term_constructor(term) == YICES_APP_TERM) {
              // Is an UF. Correct type is carried by first child.
              type = yices_type_of_term(yices_term_child(term, 0));
            } else {
              type = yices_type_of_term(term);
            }
            int[] types;
            if (yices_type_num_children(type) == 0) {
              types = new int[1];
              types[0] = type;
            } else {
              types = yices_type_children(type);
            }
            if (types.length > 0) {
              out.append("(declare-fun ");
              out.append(PrintTerm.quoteIdentifier(entry.getKey()));
              out.append(" (");
              for (int i = 0; i < types.length - 1; i++) {
                String typeDecl = yices_type_to_string(types[i]);
                typeDecl = typeDecl.substring(0, 1).toUpperCase() + typeDecl.substring(1);
                out.append(typeDecl);
                if (i + 1 < types.length - 1) {
                  out.append(' ');
                }
              }
              out.append(") ");
              String retDecl = yices_type_to_string(types[types.length - 1]);
              retDecl = retDecl.substring(0, 1).toUpperCase() + retDecl.substring(1);
              out.append(retDecl);
              out.append(")\n");
            }
          }
        }
        // TODO fold formula to avoid exp. overhead
        out.append("(assert " + yices_term_to_string(formula) + ")");
      }
    };
  }
}
