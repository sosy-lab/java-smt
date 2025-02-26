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
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

public class SolverLessFormulaManager
    extends AbstractFormulaManager<DummyFormula, DummyType, DummyEnv, DummyFunction> {

  protected SolverLessFormulaManager(
      SolverLessFormulaCreator pCreator, SolverLessBooleanFormulaManager bmgr) {
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
        null);
  }

  @Override
  public Appender dumpFormula(final DummyFormula formula) {
    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        dumpFormulaInternal(formula, out);
      }

      private void dumpFormulaInternal(DummyFormula pFormula, Appendable out) throws IOException {
        switch (pFormula.getFormulaType().myType) {
          case BOOLEAN:
            out.append(pFormula.toString());
            break;
          case INTEGER:
          case RATIONAL:
            out.append(pFormula.getValue());
            break;
          case BITVECTOR:
            out.append("(declare-const ")
                .append(pFormula.getName())
                .append(" (_ BitVec ")
                .append(String.valueOf(pFormula.getBitvectorLength()))
                .append("))");
            break;
          case FLOATING_POINT:
            out.append("(declare-const ")
                .append(pFormula.getName())
                .append(" (FloatingPoint ")
                .append(String.valueOf(pFormula.getExponent()))
                .append(" ")
                .append(String.valueOf(pFormula.getMantissa()))
                .append("))");
            break;
          case ARRAY:
            out.append("(declare-fun ")
                .append(pFormula.getName())
                .append(" () (Array ")
                .append(pFormula.getFirstArrayParameter().getFormulaType().myType.name())
                .append(" ")
                .append(pFormula.getSecondArrayParameter().getFormulaType().myType.name())
                .append("))");
            break;
          default:
            throw new UnsupportedOperationException(
                "Unsupported type: " + pFormula.getFormulaType());
        }
      }
    };
  }

  @SuppressWarnings("StringSplitter")
  @Override
  public DummyFormula parse(String smtLib) throws IllegalArgumentException {
    smtLib = smtLib.trim();
    if (smtLib.startsWith("(declare-fun ")) {
      String[] parts = smtLib.substring(12, smtLib.length() - 1).split(" ");
      String name = parts[0];
      String type = parts[parts.length - 1];
      return createDummyFormulaFromTypeString(type, name);
    } else if (smtLib.startsWith("(declare-const ")) {
      String[] parts = smtLib.substring(14, smtLib.length() - 1).split(" ");
      String name = parts[0];
      String type = parts[parts.length - 1];
      return createDummyFormulaFromTypeString(type, name);
    }
    throw new IllegalArgumentException("Unsupported SMT-LIB command: " + smtLib);
  }

  @SuppressWarnings("StringSplitter")
  public static DummyFormula createDummyFormulaFromTypeString(String type, String name) {
    switch (type) {
      case "Bool":
        DummyFormula boolResult = new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
        boolResult.setName(name);
        return boolResult;
      case "Int":
        DummyFormula intResult = new DummyFormula(new DummyType(DummyType.Type.INTEGER));
        intResult.setName(name);
        return intResult;
      case "Real":
        DummyFormula realResult = new DummyFormula(new DummyType(DummyType.Type.RATIONAL));
        realResult.setName(name);
        return realResult;
      case "String":
        DummyFormula stringResult = new DummyFormula(new DummyType(DummyType.Type.RATIONAL));
        stringResult.setName(name);
        return stringResult;
      case "Regex":
        DummyFormula regexResult = new DummyFormula(new DummyType(DummyType.Type.REGEX));
        regexResult.setName(name);
        return regexResult;
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
}
