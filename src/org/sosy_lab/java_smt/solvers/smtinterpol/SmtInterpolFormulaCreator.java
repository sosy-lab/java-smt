// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableListCopy;

import com.google.common.collect.ImmutableSet;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;

class SmtInterpolFormulaCreator extends FormulaCreator<Term, Sort, Script, FunctionSymbol> {

  /** SMTInterpol does not allow using key-functions as identifiers. */
  private static final ImmutableSet<String> UNSUPPORTED_IDENTIFIERS =
      ImmutableSet.of("true", "false", "select", "store", "or", "and", "xor", "distinct");

  SmtInterpolFormulaCreator(final Script env) {
    super(
        env,
        env.getTheory().getBooleanSort(),
        env.getTheory().getNumericSort(),
        env.getTheory().getRealSort(),
        null,
        null);
  }

  @Override
  public FormulaType<?> getFormulaType(final Term pFormula) {
    return getFormulaTypeOfSort(pFormula.getSort());
  }

  private FormulaType<?> getFormulaTypeOfSort(final Sort pSort) {
    if (pSort == getIntegerType()) {
      return FormulaType.IntegerType;
    } else if (pSort == getRationalType()) {
      return FormulaType.RationalType;
    } else if (pSort == getBoolType()) {
      return FormulaType.BooleanType;
    } else if (pSort.isArraySort()) {
      return FormulaType.getArrayType(
          getFormulaTypeOfSort(pSort.getArguments()[0]),
          getFormulaTypeOfSort(pSort.getArguments()[1]));
    } else if (pSort.isBitVecSort()) {
      return FormulaType.getBitvectorTypeWithSize(Integer.parseInt(pSort.getIndices()[0]));
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
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    } else if (pFormula instanceof BitvectorFormula) {
      Sort bvSort = extractInfo(pFormula).getSort();
      return (FormulaType<T>)
          FormulaType.getBitvectorTypeWithSize(Integer.parseInt(bvSort.getIndices()[0]));
    } else {
      return super.getFormulaType(pFormula);
    }
  }

  @Override
  public Term makeVariable(final Sort type, final String varName) {
    declareFun(varName, new Sort[] {}, type);
    return environment.term(varName);
  }

  /**
   * This function declares a new functionSymbol, that has a given (result-) sort. The params for
   * the functionSymbol also have sorts. If you want to declare a new variable, i.e. "X", paramSorts
   * is an empty array.
   */
  @CanIgnoreReturnValue
  private FunctionSymbol declareFun(String fun, Sort[] paramSorts, Sort resultSort) {
    checkSymbol(fun);

    Map<String, FunctionSymbol> declared = environment.getTheory().getDeclaredFunctions();
    if (declared.containsKey(fun)) {
      FunctionSymbol fsym = declared.get(fun);
      checkArgument(
          Arrays.equals(fsym.getParameterSorts(), paramSorts)
              && fsym.getReturnSort().equals(resultSort),
          "Function %s is already declared with different definition",
          fun);
      return fsym;
    } else {
      environment.declareFun(fun, paramSorts, resultSort);
      return environment.getTheory().getFunction(fun, paramSorts);
    }
  }

  /**
   * Copied from {@link NoopScript#checkSymbol}.
   *
   * <p>Check that the symbol does not contain characters that would make it impossible to use it in
   * a LoggingScript. These are | and \.
   *
   * @param symbol the symbol to check
   * @throws IllegalArgumentException if symbol contains | or \.
   */
  private void checkSymbol(String symbol) throws SMTLIBException {
    checkArgument(
        symbol.indexOf('|') == -1 && symbol.indexOf('\\') == -1, "Symbol must not contain | or \\");
    checkArgument(
        !UNSUPPORTED_IDENTIFIERS.contains(symbol),
        "SMTInterpol does not support %s as identifier.",
        symbol);
    checkArgument(
        !symbol.equals("true") && !symbol.equals("false"),
        "Cannot declare a variable named %s",
        symbol);
  }

  @Override
  public Sort getBitvectorType(final int pBitwidth) {
    return environment.getTheory().getSort("BitVec", new String[] {String.valueOf(pBitwidth)});
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
  @Override
  public Object convertValue(Term value) {
    FormulaType<?> type = getFormulaType(value);
    if (type.isBooleanType()) {
      return value.getTheory().mTrue == value;
    } else if (value instanceof ConstantTerm
        && ((ConstantTerm) value).getValue() instanceof Rational) {

      /*
       * From SmtInterpol documentation (see {@link ConstantTerm#getValue}),
       * the output is SmtInterpol's Rational unless it is a bitvector.
       */
      Rational rationalValue = (Rational) ((ConstantTerm) value).getValue();
      org.sosy_lab.common.rationals.Rational ratValue =
          org.sosy_lab.common.rationals.Rational.of(
              rationalValue.numerator(), rationalValue.denominator());
      return ratValue.isIntegral() ? ratValue.getNum() : ratValue;
    } else if (value instanceof ConstantTerm
        && ((ConstantTerm) value).getValue() instanceof BigInteger) {
      // SmtInterpol returns Bitvectors as BigInteger values
      return ((ConstantTerm) value).getValue();
    } else {
      throw new IllegalArgumentException("Unexpected value: " + value);
    }
  }

  /** ApplicationTerms can be wrapped with "|". This function removes those chars. */
  public static String dequote(String s) {
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
        if ((input.getSort().getName().equals("Int") && rat.isIntegral())
            || BigInteger.ONE.equals(rat.denominator())) {
          outValue = rat.numerator();
        } else {
          outValue = org.sosy_lab.common.rationals.Rational.of(rat.numerator(), rat.denominator());
        }
      } else if (interpolValue instanceof String) {
        outValue = new BigInteger(((String) interpolValue).substring(2), 2);
      } else if (interpolValue instanceof BigInteger) {
        outValue = interpolValue;
      } else {
        throw new IllegalArgumentException("Unknown constant type");
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
        final List<FormulaType<?>> argTypes;
        final Term definition = func.getDefinition();
        if (definition == null) { // generic function application, e.g., EQUALS
          argTypes = transformedImmutableListCopy(args, this::getFormulaType);
        } else {
          Sort[] paramSorts = ((ApplicationTerm) definition).getFunction().getParameterSorts();
          argTypes = transformedImmutableListCopy(paramSorts, this::getFormulaTypeOfSort);
        }

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
      case "const":
        return FunctionDeclarationKind.CONST;
      case "*":
        return FunctionDeclarationKind.MUL;
      case "+":
        return FunctionDeclarationKind.ADD;
      case "-":
        return FunctionDeclarationKind.SUB;
      case "/":
      case "div":
        return FunctionDeclarationKind.DIV;
      case "%":
      case "mod":
        return FunctionDeclarationKind.MODULO;
      case "<":
        return FunctionDeclarationKind.LT;
      case "<=":
        return FunctionDeclarationKind.LTE;
      case ">":
        return FunctionDeclarationKind.GT;
      case ">=":
        return FunctionDeclarationKind.GTE;
      case "to_int":
        return FunctionDeclarationKind.FLOOR;
      case "to_real":
        return FunctionDeclarationKind.TO_REAL;
      case "bvneg":
        return FunctionDeclarationKind.BV_NEG;
      case "bvadd":
        return FunctionDeclarationKind.BV_ADD;
      case "bvsub":
        return FunctionDeclarationKind.BV_SUB;
      case "bvsdiv":
        return FunctionDeclarationKind.BV_SDIV;
      case "bvudiv":
        return FunctionDeclarationKind.BV_UDIV;
      case "bvsrem":
        return FunctionDeclarationKind.BV_SREM;
      case "bvurem":
        return FunctionDeclarationKind.BV_UREM;
      case "bvsmod":
        return FunctionDeclarationKind.BV_SMOD;
      case "bvmul":
        return FunctionDeclarationKind.BV_MUL;
      case "bvsgt":
        return FunctionDeclarationKind.BV_SGT;
      case "bvugt":
        return FunctionDeclarationKind.BV_UGT;
      case "bvsge":
        return FunctionDeclarationKind.BV_SGE;
      case "bvuge":
        return FunctionDeclarationKind.BV_UGE;
      case "bvslt":
        return FunctionDeclarationKind.BV_SLT;
      case "bvult":
        return FunctionDeclarationKind.BV_ULT;
      case "bvsle":
        return FunctionDeclarationKind.BV_SLE;
      case "bvule":
        return FunctionDeclarationKind.BV_ULE;
      case "bvnot":
        return FunctionDeclarationKind.BV_NOT;
      case "bvand":
        return FunctionDeclarationKind.BV_AND;
      case "bvor":
        return FunctionDeclarationKind.BV_OR;
      case "bvxor":
        return FunctionDeclarationKind.BV_XOR;
      case "bvlshr":
        return FunctionDeclarationKind.BV_LSHR;
      case "bvshl":
        return FunctionDeclarationKind.BV_SHL;
      case "concat":
        return FunctionDeclarationKind.BV_CONCAT;
      case "extract":
        return FunctionDeclarationKind.BV_EXTRACT;
      default:
        // TODO: other declaration kinds!
        return FunctionDeclarationKind.OTHER;
    }
  }

  @Override
  public FunctionSymbol declareUFImpl(String pName, Sort returnType, List<Sort> pArgs) {
    Sort[] types = pArgs.toArray(new Sort[0]);
    return declareFun(pName, types, returnType);
  }

  @Override
  public Term callFunctionImpl(FunctionSymbol declaration, List<Term> args) {

    // add an explicit cast from INT to RATIONAL if needed
    final List<Term> castedArgs = new ArrayList<>();
    for (int i = 0; i < args.size(); i++) {
      // for chainable functions like EQ, DISTINCT, ADD, we repeat the last argument-type
      int index = Math.min(i, declaration.getParameterSorts().length - 1);
      Term arg = args.get(i);
      Sort argSort = arg.getSort();
      Sort paramSort = declaration.getParameterSorts()[index];
      if (getRationalType() == paramSort && getIntegerType() == argSort) {
        arg = environment.term("to_real", arg);
      }
      castedArgs.add(arg);
    }

    return environment.getTheory().term(declaration, castedArgs.toArray(new Term[0]));
  }

  @Override
  protected FunctionSymbol getBooleanVarDeclarationImpl(Term pTerm) {
    assert pTerm instanceof ApplicationTerm;
    return ((ApplicationTerm) pTerm).getFunction();
  }
}
