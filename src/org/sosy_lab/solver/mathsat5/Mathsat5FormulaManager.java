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
package org.sosy_lab.solver.mathsat5;

import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_from_smtlib2;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_to_smtlib2;

import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.basicimpl.AbstractFormulaManager;
import org.sosy_lab.solver.visitors.FormulaVisitor;

final class Mathsat5FormulaManager extends AbstractFormulaManager<Long, Long, Long> {

  @SuppressWarnings("checkstyle:parameternumber")
  Mathsat5FormulaManager(
      Mathsat5FormulaCreator creator,
      Mathsat5UnsafeFormulaManager unsafeManager,
      Mathsat5FunctionFormulaManager pFunctionManager,
      Mathsat5BooleanFormulaManager pBooleanManager,
      Mathsat5IntegerFormulaManager pIntegerManager,
      Mathsat5RationalFormulaManager pRationalManager,
      Mathsat5BitvectorFormulaManager pBitpreciseManager,
      Mathsat5FloatingPointFormulaManager pFloatingPointManager,
      Mathsat5ArrayFormulaManager pArrayManager) {
    super(
        creator,
        unsafeManager,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitpreciseManager,
        pFloatingPointManager,
        null,
        pArrayManager);
  }

  static long getMsatTerm(Formula pT) {
    return ((Mathsat5Formula) pT).getTerm();
  }

  BooleanFormula encapsulateBooleanFormula(long t) {
    return getFormulaCreator().encapsulateBoolean(t);
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    long f = msat_from_smtlib2(getEnvironment(), pS);
    return encapsulateBooleanFormula(f);
  }

  @Override
  public Appender dumpFormula(final Long f) {
    assert getFormulaCreator().getFormulaType(f) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    // Lazy invocation of msat_to_smtlib2 wrapped in an Appender.
    return Appenders.fromToStringMethod(
        new Object() {
          @Override
          public String toString() {
            String msatString = msat_to_smtlib2(getEnvironment(), f);
            StringBuilder smtString = new StringBuilder();
            boolean needsLinebreak = true;
            for (String part : msatString.split("\n")) {
              smtString.append(part);
              if (part.startsWith("(assert")) {
                needsLinebreak = false;
              }
              if (needsLinebreak) {
                smtString.append("\n");
              }
            }
            return smtString.toString();
          }
        });
  }

  @Override
  public <R> R visit(FormulaVisitor<R> rFormulaVisitor, Formula f) {
    return getUnsafeFormulaManager().visit(rFormulaVisitor, f);
  }
}
