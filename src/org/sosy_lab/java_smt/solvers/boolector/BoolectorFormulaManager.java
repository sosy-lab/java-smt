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

import java.io.IOException;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

final class BoolectorFormulaManager extends AbstractFormulaManager<Long, Long, Long, Long> {

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
        pArrayManager,
        null);
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    throw new UnsupportedOperationException("Boolector can not parse single formulas.");
  }

  @Override
  public Appender dumpFormula(Long pT) {
    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {

        // TODO This method only dumps the current node, i.e., in case of "symbol" we get the
        // declaration, in case of "formula with operator" we get a nice String.
        // We need to traverse the formula to declare all variables and dump all nodes.
        // We need to add the "assert" and check for redundant sub-formulas (and avoid them).

        String dump = BtorJNI.boolector_help_dump_node_smt2(getEnvironment(), pT);
        // strip removes the newline at the end of the string
        out.append(dump.strip());
      }
    };
  }

  protected static long getBtorTerm(Formula pT) {
    return ((BoolectorFormula) pT).getTerm();
  }
}
