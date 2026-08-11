/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.smtinterpol;

import static com.google.common.base.Preconditions.checkArgument;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class SmtInterpolBitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Term, Sort, Script, FunctionSymbol> {
  protected SmtInterpolBitvectorFormulaManager(
      FormulaCreator<Term, Sort, Script, FunctionSymbol> pCreator,
      AbstractBooleanFormulaManager<Term, Sort, Script, FunctionSymbol> pBmgr) {
    super(pCreator, pBmgr);
  }

  @Override
  protected Term makeBitvectorImpl(int length, Term pParam1) {
    return getFormulaCreator()
        .getEnv()
        .term("int_to_bv", new String[] {String.valueOf(length)}, null, pParam1);
  }

  @Override
  protected Term toIntegerFormulaImpl(Term pI, boolean signed) {
    return getFormulaCreator().getEnv().term(signed ? "sbv_to_int" : "ubv_to_int", pI);
  }

  @Override
  protected Term negate(Term pParam1) {
    return getFormulaCreator().getEnv().term("bvneg", pParam1);
  }

  @Override
  protected Term add(Term pParam1, Term pParam2) {
    return getFormulaCreator().getEnv().term("bvadd", pParam1, pParam2);
  }

  @Override
  protected Term subtract(Term pParam1, Term pParam2) {
    return getFormulaCreator().getEnv().term("bvsub", pParam1, pParam2);
  }

  @Override
  protected Term divide(Term pParam1, Term pParam2, boolean signed) {
    return getFormulaCreator().getEnv().term(signed ? "bvsdiv" : "bvudiv", pParam1, pParam2);
  }

  @Override
  protected Term remainder(Term pParam1, Term pParam2, boolean signed) {
    return getFormulaCreator().getEnv().term(signed ? "bvsrem" : "bvurem", pParam1, pParam2);
  }

  @Override
  protected Term smodulo(Term pParam1, Term pParam2) {
    return getFormulaCreator().getEnv().term("bvsmod", pParam1, pParam2);
  }

  @Override
  protected Term multiply(Term pParam1, Term pParam2) {
    return getFormulaCreator().getEnv().term("bvmul", pParam1, pParam2);
  }

  @Override
  protected Term equal(Term pParam1, Term pParam2) {
    return getFormulaCreator().getEnv().term("=", pParam1, pParam2);
  }

  @Override
  protected Term greaterThan(Term pParam1, Term pParam2, boolean signed) {
    return getFormulaCreator().getEnv().term(signed ? "bvsgt" : "bvugt", pParam1, pParam2);
  }

  @Override
  protected Term greaterOrEquals(Term pParam1, Term pParam2, boolean signed) {
    return getFormulaCreator().getEnv().term(signed ? "bvsge" : "bvuge", pParam1, pParam2);
  }

  @Override
  protected Term lessThan(Term pParam1, Term pParam2, boolean signed) {
    return getFormulaCreator().getEnv().term(signed ? "bvslt" : "bvult", pParam1, pParam2);
  }

  @Override
  protected Term lessOrEquals(Term pParam1, Term pParam2, boolean signed) {
    return getFormulaCreator().getEnv().term(signed ? "bvsle" : "bvule", pParam1, pParam2);
  }

  @Override
  protected Term not(Term pParam1) {
    return getFormulaCreator().getEnv().term("bvnot", pParam1);
  }

  @Override
  protected Term and(Term pParam1, Term pParam2) {
    return getFormulaCreator().getEnv().term("bvand", pParam1, pParam2);
  }

  @Override
  protected Term or(Term pParam1, Term pParam2) {
    return getFormulaCreator().getEnv().term("bvor", pParam1, pParam2);
  }

  @Override
  protected Term xor(Term pParam1, Term pParam2) {
    return getFormulaCreator().getEnv().term("bvxor", pParam1, pParam2);
  }

  @Override
  protected Term makeBitvectorImpl(int pLength, BigInteger pI) {
    var raw = pI;
    if (pI.signum() < 0) {
      var positive = pI.negate();
      var value = BigInteger.ZERO;
      for (var p = 0; p < Math.max(pLength, pI.bitLength() + 1); p++) {
        if (p < positive.bitLength()) {
          value = !positive.testBit(p) ? value.setBit(p) : value;
        } else {
          value = value.setBit(p);
        }
      }
      raw = value.add(BigInteger.ONE);
    }
    checkArgument(raw.bitLength() <= pLength);
    return getFormulaCreator()
        .getEnv()
        .getTheory()
        .constant(raw, formulaCreator.getBitvectorType(pLength));
  }

  @Override
  protected Term makeVariableImpl(int pLength, String pVar) {
    return getFormulaCreator().makeVariable(getFormulaCreator().getBitvectorType(pLength), pVar);
  }

  @Override
  protected Term shiftRight(Term pNumber, Term toShift, boolean signed) {
    return getFormulaCreator().getEnv().term(signed ? "bvashr" : "bvlshr", pNumber, toShift);
  }

  @Override
  protected Term shiftLeft(Term pNumber, Term pToShift) {
    return getFormulaCreator().getEnv().term("bvshl", pNumber, pToShift);
  }

  @Override
  protected Term rotateRightByConstant(Term pNumber, int pToRotate) {
    return getFormulaCreator()
        .getEnv()
        .term("rotate_right", new String[] {String.valueOf(pToRotate)}, null, pNumber);
  }

  @Override
  protected Term rotateLeftByConstant(Term pNumber, int pToRotate) {
    return getFormulaCreator()
        .getEnv()
        .term("rotate_left", new String[] {String.valueOf(pToRotate)}, null, pNumber);
  }

  @Override
  protected Term concat(Term number, Term pAppend) {
    return getFormulaCreator().getEnv().term("concat", number, pAppend);
  }

  @Override
  protected Term extract(Term pNumber, int pMsb, int pLsb) {
    return getFormulaCreator()
        .getEnv()
        .term("extract", new String[] {String.valueOf(pMsb), String.valueOf(pLsb)}, null, pNumber);
  }

  @Override
  protected Term extend(Term pNumber, int pExtensionBits, boolean pSigned) {
    return getFormulaCreator()
        .getEnv()
        .term(
            pSigned ? "sign_extend" : "zero_extend",
            new String[] {String.valueOf(pExtensionBits)},
            null,
            pNumber);
  }
}
