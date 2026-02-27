/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3legacy;

import static org.sosy_lab.java_smt.solvers.z3legacy.Z3LegacyFormulaCreator.isOP;

import com.google.common.collect.Iterables;
import com.google.common.primitives.Longs;
import com.microsoft.z3legacy.Native;
import com.microsoft.z3legacy.enumerations.Z3_decl_kind;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Set;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

class Z3LegacyBooleanFormulaManager extends AbstractBooleanFormulaManager<Long, Long, Long, Long> {

  private final long z3context;
  private final Long z3true;
  private final Long z3false;

  Z3LegacyBooleanFormulaManager(Z3LegacyFormulaCreator creator) {
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
    if (isTrue(pParam)) {
      return z3false;
    } else if (isFalse(pParam)) {
      return z3true;
    } else if (isOP(z3context, pParam, Z3_decl_kind.Z3_OP_NOT)) {
      return Native.getAppArg(z3context, pParam, 0);
    }
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
    // Z3 does not do any simplifications,
    // so we filter "true", short-circuit on "false", and filter out (simple) redundancies.
    final Set<Long> operands = new LinkedHashSet<>();
    for (final Long operand : params) {
      if (isTrue(operand)) {
        return z3true;
      }
      if (!isFalse(operand)) {
        operands.add(operand);
      }
    }
    switch (operands.size()) {
      case 0:
        return z3false;
      case 1:
        return Iterables.getOnlyElement(operands);
      default:
        return Native.mkOr(z3context, operands.size(), Longs.toArray(operands));
    }
  }

  @Override
  protected Long andImpl(Collection<Long> params) {
    // Z3 does not do any simplifications,
    // so we filter "true", short-circuit on "false", and filter out (simple) redundancies.
    final Set<Long> operands = new LinkedHashSet<>();
    for (final Long operand : params) {
      if (isFalse(operand)) {
        return z3false;
      }
      if (!isTrue(operand)) {
        operands.add(operand);
      }
    }
    switch (operands.size()) {
      case 0:
        return z3true;
      case 1:
        return Iterables.getOnlyElement(operands);
      default:
        return Native.mkAnd(z3context, operands.size(), Longs.toArray(operands));
    }
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
    return z3true.equals(pParam);
  }

  @Override
  protected boolean isFalse(Long pParam) {
    return z3false.equals(pParam);
  }

  @Override
  protected Long ifThenElse(Long pCond, Long pF1, Long pF2) {
    if (isTrue(pCond)) {
      return pF1;
    } else if (isFalse(pCond)) {
      return pF2;
    } else if (pF1.equals(pF2)) {
      return pF1;
    } else if (isTrue(pF1) && isFalse(pF2)) {
      return pCond;
    } else if (isFalse(pF1) && isTrue(pF2)) {
      return not(pCond);
    }
    return Native.mkIte(z3context, pCond, pF1, pF2);
  }
}
