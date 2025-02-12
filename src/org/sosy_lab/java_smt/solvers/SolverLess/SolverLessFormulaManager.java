/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

package org.sosy_lab.java_smt.solvers.SolverLess;

import static org.sosy_lab.java_smt.solvers.SolverLess.DummyFormula.createDummyFormulaArrayFromString;

import java.io.IOException;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.*;
import org.sosy_lab.java_smt.solvers.SolverLess.DummyType.Type;

public class SolverLessFormulaManager
    extends AbstractFormulaManager<DummyFormula, DummyType, DummyEnv, DummyFunction> {

  protected SolverLessFormulaManager(SolverLessFormulaCreator pCreator,
                                     SolverLessBooleanFormulaManager bmgr) {
    super(
        pCreator,
        new SolverLessUFManager(pCreator),
        bmgr,
        new SolverLessIntegerFormulaManager(pCreator),
        new SolverLessRationalFormulaManager(pCreator),
        new SolverLessBitvectorFormulaManager(pCreator, bmgr),
        new SolverLessFloatingPointFormulaManager(pCreator),
        null,
        new SolverLessArrayFormulaManager(pCreator),
        null,
        new SolverLessStringFormulaManager(pCreator),
        null
    );
  }

  @Override
  public Appender dumpFormula(final DummyFormula formula) {
    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        dumpFormulaInternal(formula, out);
      }

      private void dumpFormulaInternal(DummyFormula formula, Appendable out) throws IOException {
        switch (formula.getFormulaType().myType) {
          case BOOLEAN:
            out.append(formula.toString());
            break;
          case INTEGER:
          case RATIONAL:
            out.append(formula.getValue());
            break;
          case BITVECTOR:
            out.append("(declare-const ")
                .append(formula.getName())
                .append(" (_ BitVec ")
                .append(String.valueOf(formula.getBitvectorLength()))
                .append("))");
            break;
          case FLOATING_POINT:
            out.append("(declare-const ")
                .append(formula.getName())
                .append(" (FloatingPoint ")
                .append(String.valueOf(formula.getExponent()))
                .append(" ")
                .append(String.valueOf(formula.getMantissa()))
                .append("))");
            break;
          case ARRAY:
            out.append("(declare-fun ")
                .append(formula.getName())
                .append(" () (Array ")
                .append(formula.getFirstArrayParameter().getFormulaType().myType.name())
                .append(" ")
                .append(formula.getSecondArrayParameter().getFormulaType().myType.name())
                .append("))");
            break;
          default:
            throw new UnsupportedOperationException("Unsupported type: " + formula.getFormulaType());
        }
      }
    };
  }


  @Override
  public DummyFormula parse(String smtLib) throws IllegalArgumentException {
    smtLib = smtLib.trim();
    if (smtLib.startsWith("(declare-fun ")) {
      String[] parts = smtLib.substring(12, smtLib.length() - 1).split(" ");
      String name = parts[0];
      String type = parts[parts.length - 1];

      switch (type) {
        case "Bool":
          return new DummyFormula(new DummyType(Type.BOOLEAN));
        case "Int":
          return new DummyFormula(new DummyType(Type.INTEGER));
        case "Real":
          return new DummyFormula(new DummyType(Type.RATIONAL));
        default:
          if (type.startsWith("(_ BitVec")) {
            int bitwidth = Integer.parseInt(type.replaceAll("[^0-9]", ""));
            return new DummyFormula(bitwidth);
          } else if (type.startsWith("(FloatingPoint")) {
            String[] fpParts = type.replaceAll("[^0-9,]", "").split(",");
            int exponent = Integer.parseInt(fpParts[0].trim());
            int mantissa = Integer.parseInt(fpParts[1].trim());
            return new DummyFormula(exponent, mantissa);
          } else if (type.startsWith("(Array")) {
            String[] arrayParts = type.substring(7, type.length() - 1).split(" ");
            DummyFormula indexType = createDummyFormulaArrayFromString(arrayParts[0]);
            DummyFormula elementType = createDummyFormulaArrayFromString(arrayParts[1]);
            return new DummyFormula(indexType, elementType);
          }
          throw new IllegalArgumentException("Unknown type: " + type);
      }
    }
    throw new IllegalArgumentException("Unsupported SMT-LIB command: " + smtLib);
  }

}

