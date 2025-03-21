// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import static edu.stanford.CVC4.Kind.DIVISION;
import static edu.stanford.CVC4.Kind.INTS_DIVISION;
import static edu.stanford.CVC4.Kind.INTS_MODULUS;
import static edu.stanford.CVC4.Kind.ITE;
import static edu.stanford.CVC4.Kind.MINUS;
import static edu.stanford.CVC4.Kind.MULT;
import static edu.stanford.CVC4.Kind.PLUS;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Rational;
import edu.stanford.CVC4.Type;
import edu.stanford.CVC4.vectorExpr;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
abstract class CVC4NumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        Expr, Type, ExprManager, ParamFormulaType, ResultFormulaType, Expr> {

  /**
   * CVC4 fails hard when creating Integers/Rationals instead of throwing an exception for invalid
   * number format. Thus lets check the format.
   */
  public static final Pattern INTEGER_NUMBER = Pattern.compile("(-)?(\\d)+");

  public static final Pattern RATIONAL_NUMBER = Pattern.compile("(-)?(\\d)+(.)?(\\d)*");

  /** Operators for arithmetic functions that return a numeric value. */
  private static final ImmutableSet<Kind> NUMERIC_FUNCTIONS =
      ImmutableSet.of(PLUS, MINUS, MULT, DIVISION, INTS_DIVISION, INTS_MODULUS);

  protected final ExprManager exprManager;

  CVC4NumeralFormulaManager(CVC4FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    exprManager = pCreator.getEnv();
  }

  protected abstract Type getNumeralType();

  @Override
  protected boolean isNumeral(Expr pVal) {
    return (pVal.getType().isInteger() || pVal.getType().isReal()) && pVal.isConst();
  }

  /**
   * Check whether the current term is numeric and the value of a term is determined by only
   * numerals, i.e. no variable is contained. This method should check as precisely as possible the
   * situations in which CVC4 supports arithmetic operations like multiplications.
   *
   * <p>Example: TRUE for "1", "2+3", "ite(x,2,3) and FALSE for "x", "x+2", "ite(1=2,x,0)"
   */
  boolean consistsOfNumerals(Expr val) {
    Set<Expr> finished = new HashSet<>();
    Deque<Expr> waitlist = new ArrayDeque<>();
    waitlist.add(val);
    while (!waitlist.isEmpty()) {
      Expr e = waitlist.pop();
      if (!finished.add(e)) {
        continue;
      }
      if (isNumeral(e)) {
        // true, skip and check others
      } else if (NUMERIC_FUNCTIONS.contains(e.getKind())) {
        Iterables.addAll(waitlist, e);
      } else if (ITE.equals(e.getKind())) {
        // ignore condition, just use the if- and then-case
        waitlist.add(e.getChild(1));
        waitlist.add(e.getChild(2));
      } else {
        return false;
      }
    }
    return true;
  }

  @Override
  protected Expr makeNumberImpl(long i) {
    // we connot use "new Rational(long)", because it uses "unsigned long".
    return makeNumberImpl(Long.toString(i));
  }

  @Override
  protected Expr makeNumberImpl(BigInteger pI) {
    return makeNumberImpl(pI.toString());
  }

  @Override
  protected Expr makeNumberImpl(String pI) {
    if (!RATIONAL_NUMBER.matcher(pI).matches()) {
      throw new NumberFormatException("number is not an rational value: " + pI);
    }
    return exprManager.mkConst(Rational.fromDecimal(pI));
  }

  @Override
  protected Expr makeVariableImpl(String varName) {
    Type type = getNumeralType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Expr multiply(Expr pParam1, Expr pParam2) {
    if (consistsOfNumerals(pParam1) || consistsOfNumerals(pParam2)) {
      return exprManager.mkExpr(Kind.MULT, pParam1, pParam2);
    } else {
      return super.multiply(pParam1, pParam2);
    }
  }

  @Override
  protected Expr modulo(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.INTS_MODULUS, pParam1, pParam2);
  }

  @Override
  protected Expr negate(Expr pParam1) {
    return exprManager.mkExpr(Kind.UMINUS, pParam1);
  }

  @Override
  protected Expr add(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.PLUS, pParam1, pParam2);
  }

  @Override
  protected Expr subtract(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.MINUS, pParam1, pParam2);
  }

  @Override
  protected Expr equal(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  protected Expr greaterThan(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.GT, pParam1, pParam2);
  }

  @Override
  protected Expr greaterOrEquals(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.GEQ, pParam1, pParam2);
  }

  @Override
  protected Expr lessThan(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.LT, pParam1, pParam2);
  }

  @Override
  protected Expr lessOrEquals(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.LEQ, pParam1, pParam2);
  }

  @Override
  protected Expr distinctImpl(List<Expr> pParam) {
    if (pParam.size() < 2) {
      return exprManager.mkConst(true);
    } else {
      vectorExpr param = new vectorExpr();
      pParam.forEach(param::add);
      return exprManager.mkExpr(Kind.DISTINCT, param);
    }
  }
}
