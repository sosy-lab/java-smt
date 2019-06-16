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

import com.google.common.base.Splitter;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Type;
import java.io.IOException;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class CVC4FormulaManager extends AbstractFormulaManager<Expr, Type, ExprManager, Expr> {

  CVC4FormulaManager(
      FormulaCreator<Expr, Type, ExprManager, Expr> pFormulaCreator,
      CVC4UFManager pFfmgr,
      CVC4BooleanFormulaManager pBfmgr,
      CVC4IntegerFormulaManager pIfmgr,
      CVC4RationalFormulaManager pRfmgr,
      CVC4BitvectorFormulaManager pBvfmgr,
      CVC4FloatingPointFormulaManager pFpfmgr,
      CVC4ArrayFormulaManager pAfmgr,
      CVC4SLFormulaManager pSLfmgr) {
    super(pFormulaCreator, pFfmgr, pBfmgr, pIfmgr, pRfmgr, pBvfmgr, pFpfmgr, null, pAfmgr, pSLfmgr);
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

    // Lazy invocation of msat_to_smtlib2 wrapped in an Appender.
    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        String cvc4String = f.toString();
        // Adjust line breaks: assert needs to be on last line, so we remove all following breaks.
        boolean needsLinebreak = true;
        for (String part : Splitter.on('\n').split(cvc4String)) {
          out.append(part);
          if (needsLinebreak && part.startsWith("(assert")) {
            needsLinebreak = false;
          }
          if (needsLinebreak) {
            out.append('\n');
          }
        }
      }
    };
  }
}
