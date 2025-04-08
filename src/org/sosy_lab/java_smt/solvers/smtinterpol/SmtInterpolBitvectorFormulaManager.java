/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.base.Preconditions;
import com.google.common.collect.Table;
import com.google.common.collect.TreeBasedTable;
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
  private final Script script;
  private final Table<BigInteger, Integer, Term> constantCache;

  protected SmtInterpolBitvectorFormulaManager(
      FormulaCreator<Term, Sort, Script, FunctionSymbol> pCreator,
      AbstractBooleanFormulaManager<Term, Sort, Script, FunctionSymbol> pBmgr) {
    super(pCreator, pBmgr);
    script = pCreator.getEnv();
    constantCache = TreeBasedTable.create();
  }

  @Override
  protected Term makeBitvectorImpl(int length, Term pInteger) {
    return script.term("nat2bv", new String[] {String.valueOf(length)}, null, pInteger);
  }

  @Override
  protected Term makeBitvectorImpl(int pLength, BigInteger pI) {
    if (!constantCache.contains(pI, pLength)) {
      boolean isNegative = pI.compareTo(java.math.BigInteger.ZERO) < 0;
      Preconditions.checkArgument(pI.bitLength() <= (isNegative ? (pLength - 1) : pLength));

      BigInteger signedValue = pI.abs();
      if (isNegative) {
        BigInteger mask = BigInteger.ZERO.setBit(pLength).subtract(java.math.BigInteger.ONE);
        signedValue = signedValue.xor(mask).add(BigInteger.ONE);
      }
      String rawBits = signedValue.toString(2);
      String extended = (isNegative ? "1" : "0").repeat(pLength - rawBits.length()) + rawBits;

      constantCache.put(pI, pLength, script.binary("#b" + extended));
    }
    return constantCache.get(pI, pLength);
  }

  @Override
  protected Term makeVariableImpl(int pLength, String pVar) {
    Sort sort = formulaCreator.getBitvectorType(pLength);
    return formulaCreator.makeVariable(sort, pVar);
  }

  @Override
  protected Term toIntegerFormulaImpl(Term pI, boolean signed) {
    if (!signed) {
      return script.term("bv2nat", pI);
    } else {
      // Create a zero bitvector with matching bit-size
      Term zero = script.binary("#b" + "0".repeat(Integer.parseInt(pI.getSort().getIndices()[0])));

      // If the value is negative, we first negate it, then convert to integer, and after that we
      // negate again. If it is positive, we just convert directly.
      return script
          .getTheory()
          .ifthenelse(
              lessThan(pI, zero, true),
              script.term(
                  "*", script.numeral("-1"), script.term("bv2nat", script.term("bvneg", pI))),
              script.term("bv2nat", pI));
    }
  }

  @Override
  protected Term negate(Term pParam1) {
    return script.term("bvneg", pParam1);
  }

  @Override
  protected Term add(Term pParam1, Term pParam2) {
    return script.term("bvadd", pParam1, pParam2);
  }

  @Override
  protected Term subtract(Term pParam1, Term pParam2) {
    return script.term("bvsub", pParam1, pParam2);
  }

  @Override
  protected Term divide(Term pParam1, Term pParam2, boolean signed) {
    return script.term(signed ? "bvsdiv" : "bvudiv", pParam1, pParam2);
  }

  @Override
  protected Term remainder(Term pParam1, Term pParam2, boolean signed) {
    return script.term(signed ? "bvsrem" : "bvurem", pParam1, pParam2);
  }

  @Override
  protected Term smodulo(Term pParam1, Term pParam2) {
    return script.term("bvsmod", pParam1, pParam2);
  }

  @Override
  protected Term multiply(Term pParam1, Term pParam2) {
    return script.term("bvmul", pParam1, pParam2);
  }

  @Override
  protected Term equal(Term pParam1, Term pParam2) {
    return script.term("=", pParam1, pParam2);
  }

  @Override
  protected Term greaterThan(Term pParam1, Term pParam2, boolean signed) {
    return script.term(signed ? "bvsgt" : "bvugt", pParam1, pParam2);
  }

  @Override
  protected Term greaterOrEquals(Term pParam1, Term pParam2, boolean signed) {
    return script.term(signed ? "bvsge" : "bvuge", pParam1, pParam2);
  }

  @Override
  protected Term lessThan(Term pParam1, Term pParam2, boolean signed) {
    return script.term(signed ? "bvslt" : "bvult", pParam1, pParam2);
  }

  @Override
  protected Term lessOrEquals(Term pParam1, Term pParam2, boolean signed) {
    return script.term(signed ? "bvsle" : "bvule", pParam1, pParam2);
  }

  @Override
  protected Term not(Term pParam1) {
    return script.term("bvnot", pParam1);
  }

  @Override
  protected Term and(Term pParam1, Term pParam2) {
    return script.term("bvand", pParam1, pParam2);
  }

  @Override
  protected Term or(Term pParam1, Term pParam2) {
    return script.term("bvor", pParam1, pParam2);
  }

  @Override
  protected Term xor(Term pParam1, Term pParam2) {
    return script.term("bvxor", pParam1, pParam2);
  }

  @Override
  protected Term shiftRight(Term pNumber, Term pToShift, boolean signed) {
    return script.term("bvlshr", pNumber, pToShift);
  }

  @Override
  protected Term shiftLeft(Term pNumber, Term pToShift) {
    return script.term("bvshl", pNumber, pToShift);
  }

  @Override
  protected Term concat(Term pFirst, Term pSecond) {
    return script.term("concat", pFirst, pSecond);
  }

  @Override
  protected Term extract(Term pNumber, int pMsb, int pLsb) {
    return script.term(
        "extract",
        new String[] {String.valueOf(pMsb), java.lang.String.valueOf(pLsb)},
        null,
        pNumber);
  }

  @Override
  protected Term extend(Term pNumber, int pExtensionBits, boolean pSigned) {
    return script.term(
        pSigned ? "sign_extend" : "zero_extend",
        new String[] {String.valueOf(pExtensionBits)},
        null,
        pNumber);
  }
}
