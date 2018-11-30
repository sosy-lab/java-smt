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
package org.sosy_lab.java_smt.solvers.smtinterpol;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableListCopy;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import java.util.List;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;

class SmtInterpolFormulaCreator
    extends FormulaCreator<Term, Sort, SmtInterpolEnvironment, FunctionSymbol> {

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

  /** convert a boolean or numeral term into an object of type Boolean, BigInteger, or Rational. */
  Object convertValue(Term value) {
    FormulaType<?> type = getFormulaType(value);
    if (type.isBooleanType()) {
      return value.getTheory().mTrue == value;
    } else if (value instanceof ConstantTerm
        && ((ConstantTerm) value).getValue() instanceof Rational) {

      /*
       * From SmtInterpol documentation (see {@link ConstantTerm#getValue}),
       * the output is SmtInterpol's Rational unless it is a bitvector,
       * and currently we do not support bitvectors for SmtInterpol.
       */
      Rational rationalValue = (Rational) ((ConstantTerm) value).getValue();
      org.sosy_lab.common.rationals.Rational out =
          org.sosy_lab.common.rationals.Rational.of(
              rationalValue.numerator(), rationalValue.denominator());
      if (getFormulaTypeOfSort(value.getSort()).isIntegerType()) {
        assert out.isIntegral();
        return out.getNum();
      } else {
        return out;
      }
    } else {
      throw new IllegalArgumentException("Unexpected value: " + value);
    }
  }

  /** ApplicationTerms can be wrapped with "|". This function removes those chars. */
  private String dequote(String s) {
    int l = s.length();
    if (s.charAt(0) == '|' && s.charAt(l - 1) == '|') {
      return s.substring(1, l - 1);
    }
    return s;
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula f, final Term input) {
    checkArgument(
        input.getTheory().equals(environment.getTheory()),
        "Given term belongs to a different instance of SMTInterpol: %s",
        input);

    if (input instanceof ConstantTerm) {
      Object outValue;
      Object interpolValue = ((ConstantTerm) input).getValue();
      if (interpolValue instanceof Rational) {
        Rational rat = (Rational) interpolValue;
        if (input.getSort().getName().equals("Int") && rat.isIntegral()) {
          outValue = rat.numerator();
        } else {
          outValue = org.sosy_lab.common.rationals.Rational.of(rat.numerator(), rat.denominator());
        }
      } else {
        outValue = ((ConstantTerm) input).getValue();
      }
      return visitor.visitConstant(f, outValue);
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
        List<Formula> args =
            transformedImmutableListCopy(
                app.getParameters(), term -> encapsulate(getFormulaType(term), term));
        List<FormulaType<?>> argTypes = transformedImmutableListCopy(args, this::getFormulaType);

        // Any function application.
        return visitor.visitFunction(
            f,
            args,
            FunctionDeclarationImpl.of(
                name, getDeclarationKind(app), argTypes, getFormulaType(f), app.getFunction()));
      }

    } else {
      // TODO: support for quantifiers and bound variables

      throw new UnsupportedOperationException(
          String.format(
              "Unexpected SMTInterpol formula of type %s: %s",
              input.getClass().getSimpleName(), input));
    }
  }

  String getName(Term t) {
    if (isUF(t)) {
      assert t instanceof ApplicationTerm;
      return ((ApplicationTerm) t).getFunction().getName();
    } else {
      return dequote(t.toString());
    }
  }

  private static boolean isVariable(Term t) {
    // A variable is the same as an UF without parameters
    return t.getTheory().mTrue != t
        && t.getTheory().mFalse != t
        && (t instanceof ApplicationTerm)
        && ((ApplicationTerm) t).getParameters().length == 0
        && ((ApplicationTerm) t).getFunction().getDefinition() == null;
  }

  private static boolean isUF(Term t) {
    if (!(t instanceof ApplicationTerm)) {
      return false;
    }
    ApplicationTerm applicationTerm = (ApplicationTerm) t;
    FunctionSymbol func = applicationTerm.getFunction();
    return applicationTerm.getParameters().length > 0 && !func.isIntern() && !func.isInterpreted();
  }

  private FunctionDeclarationKind getDeclarationKind(ApplicationTerm input) {
    assert !isVariable(input) : "Variables should be handled somewhere else";

    FunctionSymbol symbol = input.getFunction();
    Theory t = input.getTheory();
    if (isUF(input)) {
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
    }

    // Polymorphic function symbols are more difficult.
    switch (symbol.getName()) {
      case "=":
        return FunctionDeclarationKind.EQ;
      case "distinct":
        return FunctionDeclarationKind.DISTINCT;
      case "ite":
        return FunctionDeclarationKind.ITE;
      case "select":
        return FunctionDeclarationKind.SELECT;
      case "store":
        return FunctionDeclarationKind.STORE;
      default:
        // TODO: other declaration kinds!
        return FunctionDeclarationKind.OTHER;
    }
  }

  @Override
  public FunctionSymbol declareUFImpl(String pName, Sort returnType, List<Sort> pArgs) {
    Sort[] types = pArgs.toArray(new Sort[pArgs.size()]);
    return environment.declareFun(pName, types, returnType);
  }

  @Override
  public Term callFunctionImpl(FunctionSymbol declaration, List<Term> args) {
    return environment.term(declaration.getName(), args.toArray(new Term[args.size()]));
  }

  @Override
  protected FunctionSymbol getBooleanVarDeclarationImpl(Term pTerm) {
    assert pTerm instanceof ApplicationTerm;
    return ((ApplicationTerm) pTerm).getFunction();
  }
}
