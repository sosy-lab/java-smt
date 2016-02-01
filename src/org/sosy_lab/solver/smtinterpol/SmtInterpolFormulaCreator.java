/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.smtinterpol;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.base.Function;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

import org.sosy_lab.solver.api.ArrayFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.FunctionDeclarationKind;
import org.sosy_lab.solver.basicimpl.FormulaCreator;
import org.sosy_lab.solver.basicimpl.ObjectArrayBackedList;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

class SmtInterpolFormulaCreator extends FormulaCreator<Term, Sort, SmtInterpolEnvironment> {

  private final Sort booleanSort;
  private final Sort integerSort;
  private final Sort realSort;

  SmtInterpolFormulaCreator(final SmtInterpolEnvironment env) {
    super(env, env.getBooleanSort(), env.getIntegerSort(), env.getRealSort());
    booleanSort = env.getBooleanSort();
    integerSort = env.getIntegerSort();
    realSort = env.getRealSort();
  }

  @Override
  public FormulaType<?> getFormulaType(final Term pFormula) {
    return getFormulaTypeOfSort(pFormula.getSort());
  }

  private FormulaType<?> getFormulaTypeOfSort(final Sort pSort) {
    if (pSort == integerSort) {
      return FormulaType.IntegerType;
    } else if (pSort == realSort) {
      return FormulaType.RationalType;
    } else if (pSort == booleanSort) {
      return FormulaType.BooleanType;
    } else if (pSort.isArraySort()) {
      return new FormulaType.ArrayFormulaType<>(
          getFormulaTypeOfSort(pSort.getArguments()[0]),
          getFormulaTypeOfSort(pSort.getArguments()[1]));
    } else {
      throw new IllegalArgumentException("Unknown formula type for sort: " + pSort);
    }
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(final T pFormula) {
    if (pFormula instanceof ArrayFormula<?, ?>) {
      final FormulaType<?> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<?, ?>) pFormula);
      final FormulaType<?> arrayElementType =
          getArrayFormulaElementType((ArrayFormula<?, ?>) pFormula);
      return (FormulaType<T>) new ArrayFormulaType<>(arrayIndexType, arrayElementType);
    }

    return super.getFormulaType(pFormula);
  }

  @Override
  public Term makeVariable(final Sort type, final String varName) {
    SmtInterpolEnvironment env = getEnv();
    env.declareFun(varName, new Sort[] {}, type);
    return env.term(varName);
  }

  @Override
  public Sort getBitvectorType(final int pBitwidth) {
    throw new UnsupportedOperationException(
        "Bitvector theory is not supported " + "by SmtInterpol");
  }

  @Override
  public Sort getFloatingPointType(final FormulaType.FloatingPointType type) {
    throw new UnsupportedOperationException(
        "FloatingPoint theory is not " + "supported by SmtInterpol");
  }

  @Override
  public Sort getArrayType(final Sort pIndexType, final Sort pElementType) {
    return getEnv().getTheory().getSort("Array", pIndexType, pElementType);
  }

  List<Formula> encapsulate(Term[] terms) {
    return new ObjectArrayBackedList<Term, Formula>(terms) {
      @Override
      protected Formula convert(Term pInput) {
        return encapsulate(getFormulaType(pInput), pInput);
      }
    };
  }

  /**
   * ApplicationTerms can be wrapped with "|".
   * This function removes those chars.
   **/
  private String dequote(String s) {
    int l = s.length();
    if (s.charAt(0) == '|' && s.charAt(l - 1) == '|') {
      return s.substring(1, l - 1);
    }
    return s;
  }

  private Term replaceArgs(Term pT, List<Term> newArgs) {
    return SmtInterpolUtil.replaceArgs(getEnv(), pT, SmtInterpolUtil.toTermArray(newArgs));
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula f, final Term input) {
    checkArgument(
        input.getTheory().equals(environment.getTheory()),
        "Given term belongs to a different instance of SMTInterpol: %s",
        input);

    if (input instanceof ConstantTerm) {
      final Number value = toNumber(input);
      return visitor.visitConstant(f, value);

    } else if (input instanceof ApplicationTerm) {
      final ApplicationTerm app = (ApplicationTerm) input;
      final int arity = app.getParameters().length;
      final FunctionSymbol func = app.getFunction();

      if (arity == 0) {
        if (app.equals(environment.getTheory().mTrue)) {
          return visitor.visitConstant(f, Boolean.TRUE);
        } else if (app.equals(environment.getTheory().mFalse)) {
          return visitor.visitConstant(f, Boolean.FALSE);
        } else if (func.getDefinition() == null) {
          return visitor.visitFreeVariable(f, dequote(input.toString()));
        } else {
          throw new UnsupportedOperationException("Unexpected nullary function " + input);
        }

      } else {
        final String name = func.getName();
        final List<Formula> args = encapsulate(app.getParameters());

        // Any function application.
        Function<List<Formula>, Formula> constructor =
            new Function<List<Formula>, Formula>() {
              @Override
              public Formula apply(List<Formula> formulas) {
                return encapsulateWithTypeOf(replaceArgs(input, extractInfo(formulas)));
              }
            };
        return visitor.visitFunction(
            f, args, FunctionDeclaration.of(name, getDeclarationKind(app)), constructor);
      }

    } else {
      // TODO: support for quantifiers and bound variables

      throw new UnsupportedOperationException(
          String.format(
              "Unexpected SMTInterpol formula of type %s: %s",
              input.getClass().getSimpleName(),
              input));
    }
  }

  /** check for ConstantTerm with Number or
   * ApplicationTerm with negative Number */
  public boolean isNumber(Term t) {
    boolean is = false;
    // ConstantTerm with Number --> "123"
    if (t instanceof ConstantTerm) {
      Object value = ((ConstantTerm) t).getValue();
      if (value instanceof Number || value instanceof Rational) {
        is = true;
      }

    } else if (t instanceof ApplicationTerm) {
      ApplicationTerm at = (ApplicationTerm) t;

      // ApplicationTerm with negative Number --> "(- 123)"
      if ("-".equals(at.getFunction().getName())
          && (at.getParameters().length == 1)
          && isNumber(at.getParameters()[0])) {
        is = true;

        // ApplicationTerm with Division --> "(/ 1 5)"
      } else if ("/".equals(at.getFunction().getName())
          && (at.getParameters().length == 2)
          && isNumber(at.getParameters()[0])
          && isNumber(at.getParameters()[1])) {
        is = true;
      }
    }

    // TODO hex or binary data, string?
    return is;
  }

  /**
   * Converts a term _which_came_from_the_model to a number.
   * From SmtInterpol documentation (see {@link ConstantTerm#getValue}),
   * the output is SmtInterpol's Rational unless it is a bitvector,
   * and currently we do not support bitvectors for SmtInterpol.
   **/
  public Number modelTermToNumber(Term t) {
    assert t instanceof ConstantTerm;
    assert ((ConstantTerm) t).getValue() instanceof Rational;
    Rational value = (Rational) ((ConstantTerm) t).getValue();
    org.sosy_lab.common.rationals.Rational out =
        org.sosy_lab.common.rationals.Rational.of(value.numerator(), value.denominator());
    if (getFormulaTypeOfSort(t.getSort()).isIntegerType()) {
      assert out.isIntegral();
      return out.getNum();
    }
    return out;
  }

  public Number toNumber(Term t) {
    // ConstantTerm with Number --> "123"
    if (t instanceof ConstantTerm) {
      Object value = ((ConstantTerm) t).getValue();
      if (value instanceof Number) {
        return (Number) value;
      } else if (value instanceof Rational) {
        Rational rat = (Rational) value;
        if (t.getSort().getName().equals("Int") && rat.isIntegral()) {
          return rat.numerator();
        }
        return org.sosy_lab.common.rationals.Rational.of(rat.numerator(), rat.denominator());
      }

      // ApplicationTerm with negative Number --> "-123"
    } else if (t instanceof ApplicationTerm) {
      ApplicationTerm at = (ApplicationTerm) t;

      if ("-".equals(at.getFunction().getName())) {
        Object value = toNumber(at.getParameters()[0]);
        if (value instanceof BigDecimal) {
          return ((BigDecimal) value).negate();
        } else if (value instanceof BigInteger) {
          return ((BigInteger) value).negate();
        } else if (value instanceof Long) {
          return -(Long) value;
        } else if (value instanceof Integer) {
          return -(Integer) value;
        } else if (value instanceof Double) {
          return -(Double) value;
        } else if (value instanceof Float) {
          return -(Float) value;
        } else if (value instanceof org.sosy_lab.common.rationals.Rational) {
          return ((org.sosy_lab.common.rationals.Rational) value).negate();
        }
      }
    }
    throw new NumberFormatException("unknown format of numeric term: " + t);
  }

  private FunctionDeclarationKind getDeclarationKind(ApplicationTerm input) {
    FunctionSymbol symbol = input.getFunction();
    Theory t = input.getTheory();
    if (SmtInterpolUtil.isUF(input)) {
      return FunctionDeclarationKind.UF;
    } else if (symbol == t.mAnd) {
      return FunctionDeclarationKind.AND;
    } else if (symbol == t.mOr) {
      return FunctionDeclarationKind.OR;
    } else if (symbol == t.mNot) {
      return FunctionDeclarationKind.NOT;
    } else if (symbol == t.mImplies) {
      return FunctionDeclarationKind.IMPLIES;
    } else if (symbol == t.mXor) {
      return FunctionDeclarationKind.XOR;

      // Polymorphic function symbols are more difficult.
    } else if (symbol.getName().equals("=")) {
      return FunctionDeclarationKind.EQ;
    } else if (symbol.getName().equals("distinct")) {
      return FunctionDeclarationKind.DISTINCT;
    } else if (symbol.getName().equals("ite")) {
      return FunctionDeclarationKind.ITE;
    } else if (SmtInterpolUtil.isVariable(input)) {
      return FunctionDeclarationKind.VAR;
    } else {

      // TODO: other declaration kinds!
      return FunctionDeclarationKind.OTHER;
    }
  }
}
