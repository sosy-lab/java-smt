// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.microsoft.z3.Native;
import java.util.Collection;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

class Z3BooleanFormulaManager extends AbstractBooleanFormulaManager<Long, Long, Long, Long> {

  private final long z3context;
  private final Long z3true;
  private final Long z3false;

  Z3BooleanFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    z3context = creator.getEnv();
    z3true = Native.mkTrue(z3context);
    Native.incRef(z3context, z3true);
    z3false = Native.mkFalse(z3context);
    Native.incRef(z3context, z3false);
  }

  @Override
  protected Long makeVariableImpl(String varName) {
    long type = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Long makeBooleanImpl(boolean pValue) {
    return pValue ? z3true : z3false;
  }

  @Override
  protected Long not(Long pParam) {
    return Native.mkNot(z3context, pParam);
  }

  @Override
  protected Long and(Long pParam1, Long pParam2) {
    if (isTrue(pParam1)) {
      return pParam2;
    } else if (isTrue(pParam2)) {
      return pParam1;
    } else if (isFalse(pParam1)) {
      return z3false;
    } else if (isFalse(pParam2)) {
      return z3false;
    } else if (Native.isEqAst(z3context, pParam1, pParam2)) {
      return pParam1;
    }
    return Native.mkAnd(z3context, 2, new long[] {pParam1, pParam2});
  }

  @Override
  protected Long or(Long pParam1, Long pParam2) {
    if (isTrue(pParam1)) {
      return z3true;
    } else if (isTrue(pParam2)) {
      return z3true;
    } else if (isFalse(pParam1)) {
      return pParam2;
    } else if (isFalse(pParam2)) {
      return pParam1;
    } else if (Native.isEqAst(z3context, pParam1, pParam2)) {
      return pParam1;
    }
    return Native.mkOr(z3context, 2, new long[] {pParam1, pParam2});
  }

  @Override
  protected Long orImpl(Collection<Long> params) {
    // Z3 does not do any simplifications, so we filter "false" and short-circuit on "true".
    final long[] operands = new long[params.size()]; // over-approximate size
    int count = 0;
    for (final Long operand : params) {
      if (isTrue(operand)) {
        return operand;
      }
      if (!isFalse(operand)) {
        operands[count] = operand;
        count++;
      }
    }
    switch (count) {
      case 0:
        return z3false;
      case 1:
        return operands[0];
      default:
        return Native.mkOr(z3context, count, operands); // we can pass partially filled array to Z3
    }
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toDisjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::or);
  }

  @Override
  protected Long andImpl(Collection<Long> params) {
    // Z3 does not do any simplifications, so we filter "true" and short-circuit on "false".
    final long[] operands = new long[params.size()]; // over-approximate size
    int count = 0;
    for (final Long operand : params) {
      if (isFalse(operand)) {
        return operand;
      }
      if (!isTrue(operand)) {
        operands[count] = operand;
        count++;
      }
    }
    switch (count) {
      case 0:
        return z3true;
      case 1:
        return operands[0];
      default:
        return Native.mkAnd(z3context, count, operands); // we can pass partially filled array to Z3
    }
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toConjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::and);
  }

  @Override
  protected Long xor(Long pParam1, Long pParam2) {
    return Native.mkXor(z3context, pParam1, pParam2);
  }

  @Override
  protected Long equivalence(Long pBits1, Long pBits2) {
    return Native.mkEq(z3context, pBits1, pBits2);
  }

  @Override
  protected Long implication(Long pBits1, Long pBits2) {
    return Native.mkImplies(z3context, pBits1, pBits2);
  }

  @Override
  protected boolean isTrue(Long pParam) {
    return Native.isEqAst(z3context, pParam, z3true);
  }

  @Override
  protected boolean isFalse(Long pParam) {
    return Native.isEqAst(z3context, pParam, z3false);
  }

  @Override
  protected Long ifThenElse(Long pCond, Long pF1, Long pF2) {
    return Native.mkIte(z3context, pCond, pF1, pF2);
  }
}
