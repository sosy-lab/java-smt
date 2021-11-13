// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 AlejandroSerranoMena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.microsoft.z3.Native;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;

class Z3StringFormulaManager extends AbstractStringFormulaManager<Long, Long, Long, Long> {

  private final long z3context;

  Z3StringFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    z3context = creator.getEnv();
  }

  @Override
  protected Long makeStringImpl(String pValue) {
    return Native.mkString(z3context, pValue);
  }

  @Override
  protected Long makeVariableImpl(String varName) {
    long type = getFormulaCreator().getStringType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Long equal(Long pParam1, Long pParam2) {
    return Native.mkEq(z3context, pParam1, pParam2);
  }

  @Override
  protected Long greaterThan(Long pParam1, Long pParam2) {
    return Native.mkGt(z3context, pParam1, pParam2);
  }

  @Override
  protected Long greaterOrEquals(Long pParam1, Long pParam2) {
    return Native.mkGe(z3context, pParam1, pParam2);
  }

  @Override
  protected Long lessThan(Long pParam1, Long pParam2) {
    return Native.mkLt(z3context, pParam1, pParam2);
  }

  @Override
  protected Long lessOrEquals(Long pParam1, Long pParam2) {
    return Native.mkLe(z3context, pParam1, pParam2);
  }

  @Override
  protected Long length(Long pParam) {
    return Native.mkSeqLength(z3context, pParam);
  }

  @Override
  protected Long concat(Long pParam1, Long pParam2) {
    return Native.mkSeqConcat(z3context, 2, new long[] {pParam1, pParam2});
  }

  @Override
  protected Long prefix(Long pParam1, Long pParam2) {
    return Native.mkSeqPrefix(z3context, pParam1, pParam2);
  }

  @Override
  protected Long suffix(Long pParam1, Long pParam2) {
    return Native.mkSeqSuffix(z3context, pParam1, pParam2);
  }

  @Override
  protected Long in(Long pParam1, Long pParam2) {
    return Native.mkSeqInRe(z3context, pParam1, pParam2);
  }

  @Override
  protected Long makeRegexImpl(String value) {
    Long str = makeStringImpl(value);
    return Native.mkSeqToRe(z3context, str);
  }

  @Override
  protected Long noneImpl() {
    return Native.mkReEmpty(z3context, formulaCreator.getRegexType());
  }

  @Override
  protected Long allImpl() {
    return Native.mkReFull(z3context, formulaCreator.getRegexType());
  }

  @Override
  protected Long allCharsImpl() {
    return makeRegexImpl(".");
  }

  @Override
  protected Long regexConcat(Long pParam1, Long pParam2) {
    return Native.mkReConcat(z3context, 2, new long[] {pParam1, pParam2});
  }

  @Override
  protected Long union(Long pParam1, Long pParam2) {
    return Native.mkReUnion(z3context, 2, new long[] {pParam1, pParam2});
  }

  @Override
  protected Long intersection(Long pParam1, Long pParam2) {
    return Native.mkReIntersect(z3context, 2, new long[] {pParam1, pParam2});
  }

  @Override
  protected Long closure(Long pParam) {
    return Native.mkReStar(z3context, pParam);
  }

  @Override
  protected Long complement(Long pParam) {
    return Native.mkReComplement(z3context, pParam);
  }
}
