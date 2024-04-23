// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl.parserInterpreter;

import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.FormulaType;

public class ParserFormula {

  @Nullable String type;
  Object javaSmt;

  @Nullable FormulaType<?> returnType;

  @Nullable List<FormulaType<?>> inputParams;

  public ParserFormula(Object pJavaSmt) {
    javaSmt = pJavaSmt;
  }

  @Nullable
  public String getType() {
    return type;
  }

  public void setType(String pType) {
    type = pType;
  }

  public Object getJavaSmt() {
    return javaSmt;
  }

  public void setJavaSmt(Object pJavaSmt) {
    javaSmt = pJavaSmt;
  }

  @Nullable
  public FormulaType<?> getReturnType() {
    return returnType;
  }

  public void setReturnType(FormulaType<?> pReturnType) {
    returnType = pReturnType;
  }

  @Nullable
  public List<FormulaType<?>> getInputParams() {
    return inputParams;
  }

  public void setInputParams(List<FormulaType<?>> pInputParams) {
    inputParams = pInputParams;
  }
}
