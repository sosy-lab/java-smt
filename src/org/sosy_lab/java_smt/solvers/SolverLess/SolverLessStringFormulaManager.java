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

import java.util.List;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;

public class SolverLessStringFormulaManager
    extends AbstractStringFormulaManager<DummyFormula, DummyType, DummyEnv, DummyFunction> {

  protected SolverLessStringFormulaManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected DummyFormula makeStringImpl(String value) {
    return new DummyFormula(new DummyType(DummyType.Type.STRING));
  }

  @Override
  protected DummyFormula makeVariableImpl(String pVar) {
    DummyFormula result = new DummyFormula(new DummyType(DummyType.Type.STRING));
    result.setName(pVar);
    return result;
  }

  @Override
  protected DummyFormula equal(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula greaterThan(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula greaterOrEquals(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula lessThan(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula lessOrEquals(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula length(DummyFormula pParam) {
    return new DummyFormula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  protected DummyFormula concatImpl(List<DummyFormula> parts) {
    return new DummyFormula(new DummyType(DummyType.Type.STRING));
  }

  @Override
  protected DummyFormula prefix(DummyFormula prefix, DummyFormula str) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula suffix(DummyFormula suffix, DummyFormula str) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula in(DummyFormula str, DummyFormula regex) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula contains(DummyFormula str, DummyFormula part) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula indexOf(DummyFormula str, DummyFormula part, DummyFormula startIndex) {
    return new DummyFormula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  protected DummyFormula charAt(DummyFormula str, DummyFormula index) {
    return new DummyFormula(new DummyType(DummyType.Type.STRING));
  }

  @Override
  protected DummyFormula substring(DummyFormula str, DummyFormula index, DummyFormula length) {
    return new DummyFormula(new DummyType(DummyType.Type.STRING));
  }

  @Override
  protected DummyFormula replace(
      DummyFormula fullStr, DummyFormula target, DummyFormula replacement) {
    return new DummyFormula(new DummyType(DummyType.Type.STRING));
  }

  @Override
  protected DummyFormula replaceAll(
      DummyFormula fullStr, DummyFormula target, DummyFormula replacement) {
    return new DummyFormula(new DummyType(DummyType.Type.STRING));
  }

  @Override
  protected DummyFormula makeRegexImpl(String value) {
    return new DummyFormula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected DummyFormula noneImpl() {
    return new DummyFormula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected DummyFormula allImpl() {
    return new DummyFormula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected DummyFormula allCharImpl() {
    return new DummyFormula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected DummyFormula range(DummyFormula start, DummyFormula end) {
    return new DummyFormula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected DummyFormula concatRegexImpl(List<DummyFormula> parts) {
    return new DummyFormula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected DummyFormula union(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected DummyFormula intersection(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected DummyFormula closure(DummyFormula pParam) {
    return new DummyFormula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected DummyFormula complement(DummyFormula pParam) {
    return new DummyFormula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected DummyFormula toIntegerFormula(DummyFormula pParam) {
    return new DummyFormula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  protected DummyFormula toStringFormula(DummyFormula pParam) {
    return new DummyFormula(new DummyType(DummyType.Type.STRING));
  }
}
