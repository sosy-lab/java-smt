/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Joiner;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Type;
import java.io.IOException;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

class CVC4FormulaManager extends AbstractFormulaManager<Expr, Type, ExprManager, Expr> {

  private final CVC4FormulaCreator creator;

  @SuppressWarnings("checkstyle:parameternumber")
  CVC4FormulaManager(
      CVC4FormulaCreator pFormulaCreator,
      CVC4UFManager pFfmgr,
      CVC4BooleanFormulaManager pBfmgr,
      CVC4IntegerFormulaManager pIfmgr,
      CVC4RationalFormulaManager pRfmgr,
      CVC4BitvectorFormulaManager pBvfmgr,
      CVC4FloatingPointFormulaManager pFpfmgr,
      CVC4ArrayFormulaManager pAfmgr,
      CVC4SLFormulaManager pSLfmgr) {
    super(pFormulaCreator, pFfmgr, pBfmgr, pIfmgr, pRfmgr, pBvfmgr, pFpfmgr, null, pAfmgr, pSLfmgr);
    creator = pFormulaCreator;
  }

  static Expr getCVC4Expr(Formula pT) {
    if (pT instanceof CVC4Formula) {
      return ((CVC4Formula) pT).getTerm();
    }
    throw new IllegalArgumentException(
        "Cannot get the formula info of type " + pT.getClass().getSimpleName() + " in the Solver!");
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    throw new UnsupportedOperationException();
  }

  @Override
  public Appender dumpFormula(Expr f) {
    assert getFormulaCreator().getFormulaType(f) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    return new Appenders.AbstractAppender() {

      @Override
      public void appendTo(Appendable out) throws IOException {

        // get all symbols
        final Map<String, Expr> allVars = new LinkedHashMap<>();
        creator.extractVariablesAndUFs(f, true, allVars::put);

        // print all symbols
        for (Entry<String, Expr> entry : allVars.entrySet()) {
          String name = entry.getKey();
          Expr var = entry.getValue();

          // escaping is stolen from SMTInterpol, lets hope this remains consistent
          out.append("(declare-fun ").append(PrintTerm.quoteIdentifier(name)).append(" (");

          // add function parameters
          List<Type> childrenTypes = new ArrayList<>();
          for (int i = 0; i < var.getNumChildren(); i++) {
            childrenTypes.add(var.getChild(i).getType());
          }
          out.append(Joiner.on(" ").join(childrenTypes));

          // and return type
          out.append(") ").append(var.getType().toString()).append(")\n");
        }

        // now add the final assert
        out.append("(assert ");
        // f.toString() does expand all nested sub-expressions and causes exponential overhead.
        // f.toStream() uses LET-expressions and is exactly what we want.
        f.toStream(
            new OutputStream() {

              @Override
              public void write(int chr) throws IOException {
                out.append(Character.valueOf((char) chr));
              }
            });
        out.append(')');
      }
    };
  }
}
