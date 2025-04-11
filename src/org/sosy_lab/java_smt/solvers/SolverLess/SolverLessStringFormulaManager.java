// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.util.List;
import java.util.regex.Pattern;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;

public class SolverLessStringFormulaManager
    extends AbstractStringFormulaManager<SMTLIB2Formula, DummyType, DummyEnv, DummyFunction> {

  protected SolverLessStringFormulaManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected SMTLIB2Formula makeStringImpl(String value) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.STRING), value);
  }

  @Override
  protected SMTLIB2Formula makeVariableImpl(String pVar) {
    SMTLIB2Formula result = new SMTLIB2Formula(new DummyType(DummyType.Type.STRING));
    result.setName(pVar);
    return result;
  }

  @Override
  protected SMTLIB2Formula equal(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula greaterThan(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula greaterOrEquals(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula lessThan(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula lessOrEquals(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula length(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  protected SMTLIB2Formula concatImpl(List<SMTLIB2Formula> parts) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.STRING));
  }

  @Override
  protected SMTLIB2Formula prefix(SMTLIB2Formula prefix, SMTLIB2Formula str) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula suffix(SMTLIB2Formula suffix, SMTLIB2Formula str) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula in(SMTLIB2Formula str, SMTLIB2Formula regex) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula contains(SMTLIB2Formula str, SMTLIB2Formula part) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula indexOf(
      SMTLIB2Formula str, SMTLIB2Formula part, SMTLIB2Formula startIndex) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  protected SMTLIB2Formula charAt(SMTLIB2Formula str, SMTLIB2Formula index) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.STRING));
  }

  @Override
  protected SMTLIB2Formula substring(
      SMTLIB2Formula str, SMTLIB2Formula index, SMTLIB2Formula length) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.STRING));
  }

  @Override
  protected SMTLIB2Formula replace(
      SMTLIB2Formula fullStr, SMTLIB2Formula target, SMTLIB2Formula replacement) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.STRING));
  }

  @Override
  protected SMTLIB2Formula replaceAll(
      SMTLIB2Formula fullStr, SMTLIB2Formula target, SMTLIB2Formula replacement) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.STRING));
  }

  @Override
  protected SMTLIB2Formula makeRegexImpl(String value) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.REGEX), value);
  }

  @Override
  protected SMTLIB2Formula noneImpl() {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected SMTLIB2Formula allImpl() {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected SMTLIB2Formula allCharImpl() {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected SMTLIB2Formula range(SMTLIB2Formula start, SMTLIB2Formula end) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected SMTLIB2Formula concatRegexImpl(List<SMTLIB2Formula> parts) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected SMTLIB2Formula union(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected SMTLIB2Formula intersection(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected SMTLIB2Formula closure(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected SMTLIB2Formula complement(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.REGEX));
  }

  @Override
  protected SMTLIB2Formula toIntegerFormula(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  protected SMTLIB2Formula toStringFormula(SMTLIB2Formula pParam) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.STRING));
  }
}
