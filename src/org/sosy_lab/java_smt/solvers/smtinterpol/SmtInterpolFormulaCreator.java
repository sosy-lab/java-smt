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

import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.basicimpl.Tokenizer;

class SmtInterpolFormulaCreator extends FormulaCreator<Term, Sort, Script, FunctionSymbol> {

  /** SMTInterpol does not allow using key-functions as identifiers. */
  private static final ImmutableSet<String> UNSUPPORTED_IDENTIFIERS =
      ImmutableSet.of("true", "false", "select", "store", "or", "and", "xor", "distinct", "_");

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
    } else if (pSort.isBitVecSort()) {
      return FormulaType.getBitvectorTypeWithSize(Integer.parseInt(pSort.getIndices()[0]));
    } else if (pSort.isArraySort()) {
      return FormulaType.getArrayType(
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
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    }
    return (FormulaType<T>) getFormulaTypeOfSort(extractInfo(pFormula).getSort());
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
    FunctionSymbol fsym = null;
    try {
      fsym = environment.getTheory().getFunction(fun, paramSorts);
    } catch (SMTLIBException e) {
      // fsym = null
    }
    if (fsym == null) {
      try {
        environment.declareFun(fun, paramSorts, resultSort);
      } catch (SMTLIBException e) {
        // can fail, if function is already declared with a different sort
        throw new IllegalArgumentException("Cannot declare function '" + fun + "'", e);
      }
      return environment.getTheory().getFunction(fun, paramSorts);
    } else {
      if (!fsym.getReturnSort().equals(resultSort)) {
        throw new IllegalArgumentException(
            "Function " + fun + " is already declared with different definition");
      }
      return fsym;
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
        !UNSUPPORTED_IDENTIFIERS.contains(symbol),
        "SMTInterpol does not support %s as identifier.",
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
    } else if (value instanceof ConstantTerm constantTerm
        && constantTerm.getValue() instanceof Rational rationalValue) {
      /*
       * From SmtInterpol documentation (see {@link ConstantTerm#getValue}),
       * the output is SmtInterpol's Rational unless it is a bitvector, even if the formula has
       * Integer type
       */
      org.sosy_lab.common.rationals.Rational ratValue =
          org.sosy_lab.common.rationals.Rational.of(
              rationalValue.numerator(), rationalValue.denominator());
      return ratValue.isIntegral() ? ratValue.getNum() : ratValue;
    } else if (value instanceof ConstantTerm constantTerm
        && constantTerm.getValue() instanceof BigDecimal decimalValue) {
      // Reals can be either rational or decimal values
      return org.sosy_lab.common.rationals.Rational.ofBigDecimal(decimalValue);

    } else if (value instanceof ConstantTerm constantTerm
        && constantTerm.getValue() instanceof BigInteger bitvectorValue) {
      // Bitvector term (_ bv0 32)
      return bitvectorValue;
    } else if (value instanceof ConstantTerm constantTerm
        && constantTerm.getValue() instanceof String bitvectorValue) {
      // Bitvector term #b1001 or #xffe
      var prefix = bitvectorValue.substring(0, 2);
      var base =
          switch (prefix) {
            case "#b" -> 2;
            case "#x" -> 16;
            default -> throw new IllegalStateException("Unexpected value: " + bitvectorValue);
          };
      return new BigInteger(bitvectorValue.substring(2), base);
    } else {
      throw new IllegalArgumentException("Unexpected value: " + value);
    }
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula f, final Term input) {
    if (input instanceof ConstantTerm constantTerm) {
      return visitor.visitConstant(f, convertValue(constantTerm));

    } else if (input instanceof ApplicationTerm app) {
      final int arity = app.getParameters().length;
      final FunctionSymbol func = app.getFunction();

      if (arity == 0) {
        if (app.equals(environment.getTheory().mTrue)) {
          return visitor.visitConstant(f, true);
        } else if (app.equals(environment.getTheory().mFalse)) {
          return visitor.visitConstant(f, false);
        } else if (func.getDefinition() == null) {
          return visitor.visitFreeVariable(f, Tokenizer.dequote(input.toString()));
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

    } else if (input instanceof QuantifiedFormula quantified) {
      var quantifier =
          switch (quantified.getQuantifier()) {
            case QuantifiedFormula.EXISTS -> Quantifier.EXISTS;
            case QuantifiedFormula.FORALL -> Quantifier.FORALL;
            default -> throw new AssertionError();
          };

      ImmutableMap.Builder<TermVariable, Term> builder = ImmutableMap.builder();
      for (TermVariable var : quantified.getVariables()) {
        builder.put(var, makeVariable(var.getSort(), var.getName()));
      }

      var newVars = builder.build();
      var newBody = substBoundVariables(newVars, quantified.getSubformula());

      return visitor.visitQuantifier(
          (BooleanFormula) f,
          quantifier,
          FluentIterable.from(newVars.values()).transform(this::encapsulateWithTypeOf).toList(),
          encapsulateBoolean(newBody));

    } else {
      throw new UnsupportedOperationException(
          "Unexpected SMTInterpol formula of type %s: %s"
              .formatted(input.getClass().getSimpleName(), input));
    }
  }

  /** Substitute bound variables with free variables. */
  private Term substBoundVariables(Map<TermVariable, Term> pSubst, Term pTerm) {
    if (pTerm instanceof ApplicationTerm application) {
      var args = application.getParameters();
      if (args.length == 0) {
        return pTerm;
      } else {
        return callFunctionImpl(
            application.getFunction(),
            FluentIterable.from(args).transform(p -> substBoundVariables(pSubst, p)).toList());
      }
    } else if (pTerm instanceof ConstantTerm constant) {
      return constant;
    } else if (pTerm instanceof TermVariable variable) {
      return pSubst.getOrDefault(variable, variable);
    } else if (pTerm instanceof AnnotatedTerm annotated) {
      throw new IllegalArgumentException("Unexpected 'annotated' term: %s".formatted(annotated));
    } else if (pTerm instanceof LambdaTerm lambda) {
      throw new IllegalArgumentException("Unexpected 'lambda' term: %s".formatted(lambda));
    } else if (pTerm instanceof LetTerm let) {
      throw new IllegalArgumentException("Unexpected 'let' term: %s".formatted(let));
    } else if (pTerm instanceof MatchTerm match) {
      throw new IllegalArgumentException("Unexpected 'match' term: %s".formatted(match));
    } else if (pTerm instanceof QuantifiedFormula quantified) {
      var bound = FluentIterable.from(quantified.getVariables()).toList();
      ImmutableMap.Builder<TermVariable, Term> newSubst = ImmutableMap.builder();
      for (var entry : pSubst.entrySet()) {
        if (!bound.contains(entry.getKey())) {
          newSubst.put(entry.getKey(), entry.getValue());
        }
      }
      return getEnv()
          .quantifier(
              quantified.getQuantifier(),
              quantified.getVariables(),
              substBoundVariables(newSubst.build(), quantified.getSubformula()));
    } else {
      throw new AssertionError();
    }
  }

  String getName(Term t) {
    if (t instanceof ApplicationTerm app && isUF(app)) {
      return app.getFunction().getName();
    } else {
      return Tokenizer.dequote(t.toString());
    }
  }

  private static boolean isVariable(Term t) {
    // A variable is the same as an UF without parameters
    return t.getTheory().mTrue != t
        && t.getTheory().mFalse != t
        && (t instanceof ApplicationTerm app)
        && app.getParameters().length == 0
        && app.getFunction().getDefinition() == null;
  }

  private static boolean isUF(Term t) {
    if (!(t instanceof ApplicationTerm applicationTerm)) {
      return false;
    }
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
    return switch (symbol.getName()) {
      case "=" -> FunctionDeclarationKind.EQ;
      case "distinct" -> FunctionDeclarationKind.DISTINCT;
      case "ite" -> FunctionDeclarationKind.ITE;
      case "select" -> FunctionDeclarationKind.SELECT;
      case "store" -> FunctionDeclarationKind.STORE;
      case "const" -> FunctionDeclarationKind.CONST;
      case "*" -> FunctionDeclarationKind.MUL;
      case "+" -> FunctionDeclarationKind.ADD;
      case "-" -> {
        var arity = input.getParameters().length;
        checkArgument(arity > 0);
        yield arity == 1 ? FunctionDeclarationKind.UMINUS : FunctionDeclarationKind.SUB;
      }
      case "/", "div" -> FunctionDeclarationKind.DIV;
      case "%", "mod" -> FunctionDeclarationKind.MODULO;
      case "<" -> FunctionDeclarationKind.LT;
      case "<=" -> FunctionDeclarationKind.LTE;
      case ">" -> FunctionDeclarationKind.GT;
      case ">=" -> FunctionDeclarationKind.GTE;
      case "to_int" -> FunctionDeclarationKind.FLOOR;
      case "to_real" -> FunctionDeclarationKind.TO_REAL;

      case "concat" -> FunctionDeclarationKind.BV_CONCAT;
      case "extract" -> FunctionDeclarationKind.BV_EXTRACT;
      case "bvnot" -> FunctionDeclarationKind.BV_NOT;
      case "bvand" -> FunctionDeclarationKind.BV_AND;
      case "bvor" -> FunctionDeclarationKind.BV_OR;
      case "bvneg" -> FunctionDeclarationKind.BV_NEG;
      case "bvadd" -> FunctionDeclarationKind.BV_ADD;
      case "bvmul" -> FunctionDeclarationKind.BV_MUL;
      case "bvudiv" -> FunctionDeclarationKind.BV_UDIV;
      case "bvurem" -> FunctionDeclarationKind.BV_UREM;
      case "bvshl" -> FunctionDeclarationKind.BV_SHL;
      case "bvlshr" -> FunctionDeclarationKind.BV_LSHR;
      case "bvnand" -> FunctionDeclarationKind.OTHER;
      case "bvnor" -> FunctionDeclarationKind.OTHER;
      case "bvxor" -> FunctionDeclarationKind.BV_XOR;
      case "bvxnor" -> FunctionDeclarationKind.OTHER;
      case "bvcomp" -> FunctionDeclarationKind.OTHER;
      case "bvsub" -> FunctionDeclarationKind.BV_SUB;
      case "bvsdiv" -> FunctionDeclarationKind.BV_SDIV;
      case "bvsrem" -> FunctionDeclarationKind.BV_SREM;
      case "bvsmod" -> FunctionDeclarationKind.BV_SMOD;
      case "bvashr" -> FunctionDeclarationKind.BV_ASHR;
      case "repeat" -> FunctionDeclarationKind.OTHER;
      case "zero_extend" -> FunctionDeclarationKind.BV_ZERO_EXTENSION;
      case "sign_extend" -> FunctionDeclarationKind.BV_SIGN_EXTENSION;
      case "rotate_left" -> FunctionDeclarationKind.BV_ROTATE_LEFT_BY_INT;
      case "rotate_right" -> FunctionDeclarationKind.BV_ROTATE_RIGHT_BY_INT;
      case "bvult" -> FunctionDeclarationKind.BV_ULT;
      case "bvule" -> FunctionDeclarationKind.BV_ULE;
      case "bvugt" -> FunctionDeclarationKind.BV_UGT;
      case "bvuge" -> FunctionDeclarationKind.BV_UGE;
      case "bvslt" -> FunctionDeclarationKind.BV_SLT;
      case "bvsle" -> FunctionDeclarationKind.BV_SLE;
      case "bvsgt" -> FunctionDeclarationKind.BV_SGT;
      case "bvsge" -> FunctionDeclarationKind.BV_SGE;
      case "ubv_to_int" -> FunctionDeclarationKind.UBV_TO_INT;
      case "sbv_to_int" -> FunctionDeclarationKind.SBV_TO_INT;
      case "int_to_bv" -> FunctionDeclarationKind.INT_TO_BV;
      case "bvnego" -> FunctionDeclarationKind.OTHER;
      case "bvuaddo" -> FunctionDeclarationKind.OTHER;
      case "bvsaddo" -> FunctionDeclarationKind.OTHER;
      case "bvumulo" -> FunctionDeclarationKind.OTHER;
      case "bvsmulo" -> FunctionDeclarationKind.OTHER;
      case "bvusubo" -> FunctionDeclarationKind.OTHER;
      case "bvssubo" -> FunctionDeclarationKind.OTHER;
      case "bvsdivo" -> FunctionDeclarationKind.OTHER;

      default ->
          // TODO: other declaration kinds!
          FunctionDeclarationKind.OTHER;
    };
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
    return environment.term(
        declaration.getName(), declaration.getIndices(), null, castedArgs.toArray(new Term[0]));
  }

  @Override
  protected FunctionSymbol getBooleanVarDeclarationImpl(Term pTerm) {
    if (pTerm instanceof ApplicationTerm app) {
      return app.getFunction();
    }
    throw new IllegalArgumentException("Expected ApplicationTerm, but got " + pTerm);
  }
}
