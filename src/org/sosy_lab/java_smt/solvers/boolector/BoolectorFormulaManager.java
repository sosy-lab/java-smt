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
package org.sosy_lab.java_smt.solvers.boolector;

import com.google.common.base.Splitter;
import java.io.IOException;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

final class BoolectorFormulaManager
    extends AbstractFormulaManager<Long, Long, BoolectorEnvironment, Long> {

  protected BoolectorFormulaManager(
      BoolectorFormulaCreator pFormulaCreator,
      BoolectorUFManager pFunctionManager,
      BoolectorBooleanFormulaManager pBooleanManager,
      BoolectorBitvectorFormulaManager pBitvectorManager,
      BoolectorQuantifiedFormulaManager pQuantifierManager,
      BoolectorArrayFormulaManager pArrayManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        null,
        null,
        pBitvectorManager,
        null,
        pQuantifierManager,
        pArrayManager);
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    throw new UnsupportedOperationException("Boolector can not parse single formulas.");
  }

  @Override
  public Appender dumpFormula(Long pT) {
    // TODO check if line break is correct!!!!
    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        String dump = BtorJNI.boolector_help_dump_node_smt2(getEnvironment().getBtor(), pT);
        // Adjust line breaks: assert needs to be on last line, so we remove all following breaks.
        boolean needsLinebreak = true;
        for (String part : Splitter.on('\n').split(dump)) {
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

  static long getBtorTerm(Formula pT) {
    return ((BoolectorFormula) pT).getTerm();
  }

}
