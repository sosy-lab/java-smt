// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_and;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_cond;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_false;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_iff;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_not;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_or;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_true;
import static org.sosy_lab.java_smt.solvers.boolector.BtorJNI.boolector_xor;

import com.google.common.primitives.Longs;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

public class BoolectorBooleanFormulaManager
    extends AbstractBooleanFormulaManager<Long, Long, Long, Long> {

  private final long btor;

  BoolectorBooleanFormulaManager(BoolectorFormulaCreator pCreator) {
    super(pCreator);
    this.btor = pCreator.getEnv();
  }

  @Override
  public Long makeVariableImpl(String varName) {
    long boolType = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(boolType, varName);
  }

  @Override
  public Long makeBooleanImpl(boolean pValue) {
    if (pValue) {
      return boolector_true(btor);
    } else {
      return boolector_false(btor);
    }
  }

  @Override
  public Long not(Long pParam1) {
    return boolector_not(btor, pParam1);
  }

  @Override
  public Long and(Long pParam1, Long pParam2) {
    return boolector_and(btor, pParam1, pParam2);
  }

  @Override
  public Long or(Long pParam1, Long pParam2) {
    return boolector_or(btor, pParam1, pParam2);
  }

  @Override
  public Long xor(Long pParam1, Long pParam2) {
    return boolector_xor(btor, pParam1, pParam2);
  }

  @Override
  public Long equivalence(Long pBits1, Long pBits2) {
    return boolector_iff(btor, pBits1, pBits2);
  }

  @Override
  public boolean isTrue(Long pBits) {
    return isConstant(pBits, 1);
  }

  @Override
  public boolean isFalse(Long pBits) {
    return isConstant(pBits, 0);
  }

  private boolean isConstant(final long pBits, final int constant) {
    if (BtorJNI.boolector_get_width(btor, pBits) == 1) {
      String assignment;
      if (BtorJNI.boolector_is_const(btor, pBits)) {
        assignment = BtorJNI.boolector_get_bits(btor, pBits);
        Long maybeLong = Longs.tryParse(assignment);
        if (maybeLong != null && maybeLong == constant) {
          return true;
        }
      }
    }
    return false;
  }

  @Override
  public Long ifThenElse(Long pCond, Long pF1, Long pF2) {
    return boolector_cond(btor, pCond, pF1, pF2);
  }
}
