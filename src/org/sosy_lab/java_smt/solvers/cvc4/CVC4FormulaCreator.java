// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.java_smt.api.FormulaType.getFloatingPointTypeFromSizesWithoutHiddenBit;
import static org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager.unescapeUnicodeForSmtlib;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import com.google.common.primitives.Ints;
import edu.stanford.CVC4.ArrayStoreAll;
import edu.stanford.CVC4.ArrayType;
import edu.stanford.CVC4.BitVectorType;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.FunctionType;
import edu.stanford.CVC4.Integer;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Rational;
import edu.stanford.CVC4.RoundingMode;
import edu.stanford.CVC4.Type;
import edu.stanford.CVC4.vectorExpr;
import edu.stanford.CVC4.vectorType;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Formula.CVC4ArrayFormula;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Formula.CVC4BitvectorFormula;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Formula.CVC4BooleanFormula;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Formula.CVC4FloatingPointFormula;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Formula.CVC4FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Formula.CVC4IntegerFormula;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Formula.CVC4RationalFormula;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Formula.CVC4RegexFormula;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Formula.CVC4StringFormula;

public class CVC4FormulaCreator extends FormulaCreator<Expr, Type, ExprManager, Expr> {

  private static final Pattern FLOATING_POINT_PATTERN =
      Pattern.compile("^\\(fp #b(?<sign>\\d) #b(?<exp>\\d+) #b(?<mant>\\d+)$");

  private final Map<String, Expr> variablesCache = new HashMap<>();
  private final Map<String, Expr> functionsCache = new HashMap<>();
  private final ExprManager exprManager;

  protected CVC4FormulaCreator(ExprManager pExprManager) {
    super(
        pExprManager,
        pExprManager.booleanType(),
        pExprManager.integerType(),
        pExprManager.realType(),
        pExprManager.stringType(),
        pExprManager.regExpType());
    exprManager = pExprManager;
  }

  @Override
  public Expr makeVariable(Type type, String name) {
    Expr exp = variablesCache.computeIfAbsent(name, n -> exprManager.mkVar(name, type));
    Preconditions.checkArgument(
        type.equals(exp.getType()),
        "symbol name already in use for different type %s",
        exp.getType());
    return exp;
  }

  /**
   * Makes a bound copy of a variable for use in quantifier. Note that all occurrences of the free
   * var have to be substituted by the bound once it exists.
   *
   * @param var Variable you want a bound copy of.
   * @return Bound Variable
   */
  public Expr makeBoundCopy(Expr var) {
    Type type = var.getType();
    String name = getName(var);
    Expr boundCopy = exprManager.mkBoundVar(name, type);
    return boundCopy;
  }

  @Override
  public Type getBitvectorType(int pBitwidth) {
    return exprManager.mkBitVectorType(pBitwidth);
  }

  @Override
  public Type getFloatingPointType(FloatingPointType pType) {
    return exprManager.mkFloatingPointType(
        pType.getExponentSize(), pType.getMantissaSizeWithHiddenBit());
  }

  @Override
  public Type getArrayType(Type pIndexType, Type pElementType) {
    return exprManager.mkArrayType(pIndexType, pElementType);
  }

  @Override
  public Expr extractInfo(Formula pT) {
    return CVC4FormulaManager.getCVC4Expr(pT);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TD extends Formula, TR extends Formula> FormulaType<TR> getArrayFormulaElementType(
      ArrayFormula<TD, TR> pArray) {
    return ((CVC4ArrayFormula<TD, TR>) pArray).getElementType();
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TD extends Formula, TR extends Formula> FormulaType<TD> getArrayFormulaIndexType(
      ArrayFormula<TD, TR> pArray) {
    return ((CVC4ArrayFormula<TD, TR>) pArray).getIndexType();
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    Type t = extractInfo(pFormula).getType();
    if (pFormula instanceof BitvectorFormula) {
      checkArgument(t.isBitVector(), "BitvectorFormula with actual type %s: %s", t, pFormula);
      return (FormulaType<T>) getFormulaType(extractInfo(pFormula));

    } else if (pFormula instanceof FloatingPointFormula) {
      checkArgument(
          t.isFloatingPoint(), "FloatingPointFormula with actual type %s: %s", t, pFormula);
      edu.stanford.CVC4.FloatingPointType fpType = new edu.stanford.CVC4.FloatingPointType(t);
      return (FormulaType<T>)
          FormulaType.getFloatingPointTypeFromSizesWithHiddenBit(
              (int) fpType.getExponentSize(), (int) fpType.getSignificandSize()); // with hidden bit

    } else if (pFormula instanceof ArrayFormula<?, ?>) {
      FormulaType<T> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<T, T>) pFormula);
      FormulaType<T> arrayElementType = getArrayFormulaElementType((ArrayFormula<T, T>) pFormula);
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    }
    return super.getFormulaType(pFormula);
  }

  @Override
  public FormulaType<?> getFormulaType(Expr pFormula) {
    return getFormulaTypeFromTermType(pFormula.getType());
  }

  private FormulaType<?> getFormulaTypeFromTermType(Type t) {
    if (t.isBoolean()) {
      return FormulaType.BooleanType;
    } else if (t.isInteger()) {
      return FormulaType.IntegerType;
    } else if (t.isBitVector()) {
      // apparently, we can get a t instanceof Type here for that t instanceof BitVectorType does
      // not hold, hence we use the new BitVectorType(t) here as a workaround:
      return FormulaType.getBitvectorTypeWithSize((int) new BitVectorType(t).getSize());
    } else if (t.isFloatingPoint()) {
      edu.stanford.CVC4.FloatingPointType fpType = new edu.stanford.CVC4.FloatingPointType(t);
      return FormulaType.getFloatingPointTypeFromSizesWithHiddenBit(
          (int) fpType.getExponentSize(), (int) fpType.getSignificandSize()); // with hidden bit
    } else if (t.isRoundingMode()) {
      return FormulaType.FloatingPointRoundingModeType;
    } else if (t.isReal()) {
      // The theory REAL in CVC4 is the theory of (infinite precision!) real numbers.
      // As such, the theory RATIONAL is contained in REAL. TODO: find a better solution.
      return FormulaType.RationalType;
    } else if (t.isArray()) {
      ArrayType arrayType = new ArrayType(t); // instead of casting, create a new type.
      FormulaType<?> indexType = getFormulaTypeFromTermType(arrayType.getIndexType());
      FormulaType<?> elementType = getFormulaTypeFromTermType(arrayType.getConstituentType());
      return FormulaType.getArrayType(indexType, elementType);
    } else if (t.isString()) {
      return FormulaType.StringType;
    } else if (t.isRegExp()) {
      return FormulaType.RegexType;
    } else {
      throw new AssertionError(
          String.format("Unhandled type '%s' with base type '%s'.", t, t.getBaseType()));
    }
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, Expr pTerm) {
    assert pType.equals(getFormulaType(pTerm))
            || (pType.equals(FormulaType.RationalType)
                && getFormulaType(pTerm).equals(FormulaType.IntegerType))
        : String.format(
            "Trying to encapsulate formula %s of type %s as %s",
            pTerm, getFormulaType(pTerm), pType);
    if (pType.isBooleanType()) {
      return (T) new CVC4BooleanFormula(pTerm);
    } else if (pType.isIntegerType()) {
      return (T) new CVC4IntegerFormula(pTerm);
    } else if (pType.isRationalType()) {
      return (T) new CVC4RationalFormula(pTerm);
    } else if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrFt = (ArrayFormulaType<?, ?>) pType;
      return (T) new CVC4ArrayFormula<>(pTerm, arrFt.getIndexType(), arrFt.getElementType());
    } else if (pType.isBitvectorType()) {
      return (T) new CVC4BitvectorFormula(pTerm);
    } else if (pType.isFloatingPointType()) {
      return (T) new CVC4FloatingPointFormula(pTerm);
    } else if (pType.isFloatingPointRoundingModeType()) {
      return (T) new CVC4FloatingPointRoundingModeFormula(pTerm);
    } else if (pType.isStringType()) {
      return (T) new CVC4StringFormula(pTerm);
    } else if (pType.isRegexType()) {
      return (T) new CVC4RegexFormula(pTerm);
    }
    throw new IllegalArgumentException("Cannot create formulas of type " + pType + " in CVC4");
  }

  private Formula encapsulate(Expr pTerm) {
    return encapsulate(getFormulaType(pTerm), pTerm);
  }

  @Override
  public BooleanFormula encapsulateBoolean(Expr pTerm) {
    assert getFormulaType(pTerm).isBooleanType()
        : String.format(
            "%s is not boolean, but %s (%s)", pTerm, pTerm.getType(), getFormulaType(pTerm));
    return new CVC4BooleanFormula(pTerm);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Expr pTerm) {
    assert getFormulaType(pTerm).isBitvectorType()
        : String.format("%s is no BV, but %s (%s)", pTerm, pTerm.getType(), getFormulaType(pTerm));
    return new CVC4BitvectorFormula(pTerm);
  }

  @Override
  protected FloatingPointFormula encapsulateFloatingPoint(Expr pTerm) {
    assert getFormulaType(pTerm).isFloatingPointType()
        : String.format("%s is no FP, but %s (%s)", pTerm, pTerm.getType(), getFormulaType(pTerm));
    return new CVC4FloatingPointFormula(pTerm);
  }

  @Override
  protected FloatingPointRoundingModeFormula encapsulateRoundingMode(Expr pTerm) {
    assert getFormulaType(pTerm).isFloatingPointRoundingModeType()
        : String.format(
            "%s is no FP rounding mode, but %s (%s)",
            pTerm, pTerm.getType(), getFormulaType(pTerm));
    return new CVC4FloatingPointRoundingModeFormula(pTerm);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      Expr pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType))
        : String.format(
            "%s is no array, but %s (%s)", pTerm, pTerm.getType(), getFormulaType(pTerm));
    return new CVC4ArrayFormula<>(pTerm, pIndexType, pElementType);
  }

  @Override
  protected StringFormula encapsulateString(Expr pTerm) {
    assert getFormulaType(pTerm).isStringType()
        : String.format(
            "%s is no String, but %s (%s)", pTerm, pTerm.getType(), getFormulaType(pTerm));
    return new CVC4StringFormula(pTerm);
  }

  @Override
  protected RegexFormula encapsulateRegex(Expr pTerm) {
    assert getFormulaType(pTerm).isRegexType();
    return new CVC4RegexFormula(pTerm);
  }

  static String getName(Expr e) {
    checkState(!e.isNull());
    if (!e.isConst() && !e.isVariable()) {
      e = e.getOperator();
    }
    return dequote(e.toString());
  }

  @SuppressWarnings("deprecation")
  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, final Expr f) {
    checkState(!f.isNull());
    Type type = f.getType();

    if (f.isConst()) {
      if (type.isBoolean()) {
        return visitor.visitConstant(formula, f.getConstBoolean());
      } else if (type.isInteger()) {
        Rational rationalValue = f.getConstRational();
        Preconditions.checkState("1".equals(rationalValue.getDenominator().toString()));
        return visitor.visitConstant(
            formula, new BigInteger(rationalValue.getNumerator().toString()));
      } else if (type.isReal()) {
        Rational rationalValue = f.getConstRational();
        return visitor.visitConstant(
            formula,
            org.sosy_lab.common.rationals.Rational.of(
                new BigInteger(rationalValue.getNumerator().toString()),
                new BigInteger(rationalValue.getDenominator().toString())));
      } else if (type.isBitVector()) {
        return visitor.visitConstant(
            formula, new BigInteger(f.getConstBitVector().getValue().toString(10)));
      } else if (type.isFloatingPoint()) {
        return visitor.visitConstant(formula, convertFloatingPoint(f));
      } else if (type.isRoundingMode()) {
        return visitor.visitConstant(formula, getRoundingMode(f));
      } else if (type.isString()) {
        return visitor.visitConstant(formula, f.getConstString().toString());
      } else if (type.isArray()) {
        ArrayStoreAll storeAll = f.getConstArrayStoreAll();
        Expr constant = storeAll.getExpr();
        return visitor.visitFunction(
            formula,
            ImmutableList.of(encapsulate(constant)),
            FunctionDeclarationImpl.of(
                getName(f),
                getDeclarationKind(f),
                ImmutableList.of(getFormulaTypeFromTermType(constant.getType())),
                getFormulaType(f),
                f.getKind()));
      } else {
        throw new UnsupportedOperationException("Unhandled constant " + f + " with type " + type);
      }

    } else if (f.getKind() == Kind.BOUND_VARIABLE) {
      // BOUND vars are used for all vars that are bound to a quantifier in CVC4.
      // We resubstitute them back to the original free.
      // CVC4 doesn't give you the de-brujin index
      Expr originalVar = variablesCache.get(formula.toString());
      return visitor.visitBoundVariable(encapsulate(originalVar), 0);

    } else if (f.getKind() == Kind.FORALL || f.getKind() == Kind.EXISTS) {
      // QUANTIFIER: replace bound variable with free variable for visitation
      assert f.getNumChildren() == 2;
      Expr body = f.getChildren().get(1);
      List<Formula> freeVars = new ArrayList<>();
      for (Expr boundVar : f.getChild(0)) { // unpack grand-children of f.
        String name = getName(boundVar);
        Expr freeVar = Preconditions.checkNotNull(variablesCache.get(name));
        body = body.substitute(boundVar, freeVar);
        freeVars.add(encapsulate(freeVar));
      }
      BooleanFormula fBody = encapsulateBoolean(body);
      Quantifier quant = f.getKind() == Kind.EXISTS ? Quantifier.EXISTS : Quantifier.FORALL;
      return visitor.visitQuantifier((BooleanFormula) formula, quant, freeVars, fBody);

    } else if (f.isVariable()) {
      assert f.getKind() != Kind.BOUND_VARIABLE;
      return visitor.visitFreeVariable(formula, getName(f));

    } else if (f.getKind() == Kind.SEP_NIL) {
      return visitor.visitConstant(formula, null);

    } else {
      // Expressions like uninterpreted function calls (Kind.APPLY_UF) or operators (e.g. Kind.AND).
      // These are all treated like operators, so we can get the declaration by f.getOperator()!
      List<Formula> args = ImmutableList.copyOf(Iterables.transform(f, this::encapsulate));
      List<FormulaType<?>> argsTypes = new ArrayList<>();
      Expr operator = normalize(f.getOperator());
      if (operator.getType().isFunction()) {
        vectorType argTypes = new FunctionType(operator.getType()).getArgTypes();
        for (int i = 0; i < argTypes.size(); i++) {
          argsTypes.add(getFormulaTypeFromTermType(argTypes.get(i)));
        }
      } else {
        for (Expr arg : f) {
          argsTypes.add(getFormulaType(arg));
        }
      }

      checkState(args.size() == argsTypes.size());

      // TODO some operations (BV_SIGN_EXTEND, BV_ZERO_EXTEND, maybe more) encode information as
      // part of the operator itself, thus the arity is one too small and there might be no
      // possibility to access the information from user side. Should we encode such information as
      // additional parameters? We do so for some methods of Princess.
      return visitor.visitFunction(
          formula,
          args,
          FunctionDeclarationImpl.of(
              getName(f), getDeclarationKind(f), argsTypes, getFormulaType(f), operator));
    }
  }

  /** CVC4 returns new objects when querying operators for UFs. The new operator */
  private Expr normalize(Expr operator) {
    Expr function = functionsCache.get(getName(operator));
    if (function != null) {
      checkState(
          function.getId().equals(operator.getId()),
          "operator '%s' with ID %s differs from existing function '%s' with ID '%s'.",
          operator,
          operator.getId(),
          function,
          function.getId());
      return function;
    }
    return operator;
  }

  // see src/theory/*/kinds in CVC4 sources for description of the different CVC4 kinds ;)
  private static final ImmutableMap<Kind, FunctionDeclarationKind> KIND_MAPPING =
      ImmutableMap.<Kind, FunctionDeclarationKind>builder()
          .put(Kind.EQUAL, FunctionDeclarationKind.EQ)
          .put(Kind.DISTINCT, FunctionDeclarationKind.DISTINCT)
          .put(Kind.NOT, FunctionDeclarationKind.NOT)
          .put(Kind.AND, FunctionDeclarationKind.AND)
          .put(Kind.IMPLIES, FunctionDeclarationKind.IMPLIES)
          .put(Kind.OR, FunctionDeclarationKind.OR)
          .put(Kind.XOR, FunctionDeclarationKind.XOR)
          .put(Kind.ITE, FunctionDeclarationKind.ITE)
          .put(Kind.APPLY_UF, FunctionDeclarationKind.UF)
          .put(Kind.PLUS, FunctionDeclarationKind.ADD)
          .put(Kind.MULT, FunctionDeclarationKind.MUL)
          .put(Kind.MINUS, FunctionDeclarationKind.SUB)
          .put(Kind.INTS_DIVISION, FunctionDeclarationKind.DIV)
          .put(Kind.INTS_MODULUS, FunctionDeclarationKind.MODULO)
          .put(Kind.DIVISION, FunctionDeclarationKind.DIV)
          .put(Kind.LT, FunctionDeclarationKind.LT)
          .put(Kind.LEQ, FunctionDeclarationKind.LTE)
          .put(Kind.GT, FunctionDeclarationKind.GT)
          .put(Kind.GEQ, FunctionDeclarationKind.GTE)
          .put(Kind.INT_TO_BITVECTOR, FunctionDeclarationKind.INT_TO_BV)
          // Bitvector theory
          .put(Kind.BITVECTOR_PLUS, FunctionDeclarationKind.BV_ADD)
          .put(Kind.BITVECTOR_SUB, FunctionDeclarationKind.BV_SUB)
          .put(Kind.BITVECTOR_MULT, FunctionDeclarationKind.BV_MUL)
          .put(Kind.BITVECTOR_AND, FunctionDeclarationKind.BV_AND)
          .put(Kind.BITVECTOR_OR, FunctionDeclarationKind.BV_OR)
          .put(Kind.BITVECTOR_XOR, FunctionDeclarationKind.BV_XOR)
          .put(Kind.BITVECTOR_SLT, FunctionDeclarationKind.BV_SLT)
          .put(Kind.BITVECTOR_ULT, FunctionDeclarationKind.BV_ULT)
          .put(Kind.BITVECTOR_SLE, FunctionDeclarationKind.BV_SLE)
          .put(Kind.BITVECTOR_ULE, FunctionDeclarationKind.BV_ULE)
          .put(Kind.BITVECTOR_SGT, FunctionDeclarationKind.BV_SGT)
          .put(Kind.BITVECTOR_UGT, FunctionDeclarationKind.BV_UGT)
          .put(Kind.BITVECTOR_SGE, FunctionDeclarationKind.BV_SGE)
          .put(Kind.BITVECTOR_UGE, FunctionDeclarationKind.BV_UGE)
          .put(Kind.BITVECTOR_SDIV, FunctionDeclarationKind.BV_SDIV)
          .put(Kind.BITVECTOR_UDIV, FunctionDeclarationKind.BV_UDIV)
          .put(Kind.BITVECTOR_SREM, FunctionDeclarationKind.BV_SREM)
          .put(Kind.BITVECTOR_UREM, FunctionDeclarationKind.BV_UREM)
          .put(Kind.BITVECTOR_SMOD, FunctionDeclarationKind.BV_SMOD)
          .put(Kind.BITVECTOR_SHL, FunctionDeclarationKind.BV_SHL)
          .put(Kind.BITVECTOR_ASHR, FunctionDeclarationKind.BV_ASHR)
          .put(Kind.BITVECTOR_LSHR, FunctionDeclarationKind.BV_LSHR)
          .put(Kind.BITVECTOR_ROTATE_LEFT, FunctionDeclarationKind.BV_ROTATE_LEFT_BY_INT)
          .put(Kind.BITVECTOR_ROTATE_RIGHT, FunctionDeclarationKind.BV_ROTATE_RIGHT_BY_INT)
          .put(Kind.BITVECTOR_NOT, FunctionDeclarationKind.BV_NOT)
          .put(Kind.BITVECTOR_NEG, FunctionDeclarationKind.BV_NEG)
          .put(Kind.BITVECTOR_EXTRACT, FunctionDeclarationKind.BV_EXTRACT)
          .put(Kind.BITVECTOR_CONCAT, FunctionDeclarationKind.BV_CONCAT)
          .put(Kind.BITVECTOR_TO_NAT, FunctionDeclarationKind.UBV_TO_INT)
          .put(Kind.BITVECTOR_SIGN_EXTEND, FunctionDeclarationKind.BV_SIGN_EXTENSION)
          .put(Kind.BITVECTOR_ZERO_EXTEND, FunctionDeclarationKind.BV_ZERO_EXTENSION)
          // Floating-point theory
          .put(Kind.TO_INTEGER, FunctionDeclarationKind.FLOOR)
          .put(Kind.FLOATINGPOINT_TO_SBV, FunctionDeclarationKind.FP_CASTTO_SBV)
          .put(Kind.FLOATINGPOINT_TO_UBV, FunctionDeclarationKind.FP_CASTTO_UBV)
          .put(Kind.FLOATINGPOINT_TO_FP_FLOATINGPOINT, FunctionDeclarationKind.FP_CASTTO_FP)
          .put(Kind.FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR, FunctionDeclarationKind.BV_SCASTTO_FP)
          .put(Kind.FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR, FunctionDeclarationKind.BV_UCASTTO_FP)
          .put(Kind.FLOATINGPOINT_ISNAN, FunctionDeclarationKind.FP_IS_NAN)
          .put(Kind.FLOATINGPOINT_ISNEG, FunctionDeclarationKind.FP_IS_NEGATIVE)
          .put(Kind.FLOATINGPOINT_ISINF, FunctionDeclarationKind.FP_IS_INF)
          .put(Kind.FLOATINGPOINT_ISN, FunctionDeclarationKind.FP_IS_NORMAL)
          .put(Kind.FLOATINGPOINT_ISSN, FunctionDeclarationKind.FP_IS_SUBNORMAL)
          .put(Kind.FLOATINGPOINT_ISZ, FunctionDeclarationKind.FP_IS_ZERO)
          .put(Kind.FLOATINGPOINT_EQ, FunctionDeclarationKind.FP_EQ)
          .put(Kind.FLOATINGPOINT_ABS, FunctionDeclarationKind.FP_ABS)
          .put(Kind.FLOATINGPOINT_MAX, FunctionDeclarationKind.FP_MAX)
          .put(Kind.FLOATINGPOINT_MIN, FunctionDeclarationKind.FP_MIN)
          .put(Kind.FLOATINGPOINT_SQRT, FunctionDeclarationKind.FP_SQRT)
          .put(Kind.FLOATINGPOINT_NEG, FunctionDeclarationKind.FP_NEG)
          .put(Kind.FLOATINGPOINT_PLUS, FunctionDeclarationKind.FP_ADD)
          .put(Kind.FLOATINGPOINT_SUB, FunctionDeclarationKind.FP_SUB)
          .put(Kind.FLOATINGPOINT_MULT, FunctionDeclarationKind.FP_MUL)
          .put(Kind.FLOATINGPOINT_DIV, FunctionDeclarationKind.FP_DIV)
          .put(Kind.FLOATINGPOINT_REM, FunctionDeclarationKind.FP_REM)
          .put(Kind.FLOATINGPOINT_LT, FunctionDeclarationKind.FP_LT)
          .put(Kind.FLOATINGPOINT_LEQ, FunctionDeclarationKind.FP_LE)
          .put(Kind.FLOATINGPOINT_GT, FunctionDeclarationKind.FP_GT)
          .put(Kind.FLOATINGPOINT_GEQ, FunctionDeclarationKind.FP_GE)
          .put(Kind.FLOATINGPOINT_RTI, FunctionDeclarationKind.FP_ROUND_TO_INTEGRAL)
          .put(Kind.FLOATINGPOINT_TO_FP_IEEE_BITVECTOR, FunctionDeclarationKind.FP_AS_IEEEBV)
          // String and Regex theory
          .put(Kind.STRING_CONCAT, FunctionDeclarationKind.STR_CONCAT)
          .put(Kind.STRING_PREFIX, FunctionDeclarationKind.STR_PREFIX)
          .put(Kind.STRING_SUFFIX, FunctionDeclarationKind.STR_SUFFIX)
          .put(Kind.STRING_STRCTN, FunctionDeclarationKind.STR_CONTAINS)
          .put(Kind.STRING_SUBSTR, FunctionDeclarationKind.STR_SUBSTRING)
          .put(Kind.STRING_STRREPL, FunctionDeclarationKind.STR_REPLACE)
          .put(Kind.STRING_STRREPLALL, FunctionDeclarationKind.STR_REPLACE_ALL)
          .put(Kind.STRING_CHARAT, FunctionDeclarationKind.STR_CHAR_AT)
          .put(Kind.STRING_LENGTH, FunctionDeclarationKind.STR_LENGTH)
          .put(Kind.STRING_STRIDOF, FunctionDeclarationKind.STR_INDEX_OF)
          .put(Kind.STRING_TO_REGEXP, FunctionDeclarationKind.STR_TO_RE)
          .put(Kind.STRING_IN_REGEXP, FunctionDeclarationKind.STR_IN_RE)
          .put(Kind.STRING_STOI, FunctionDeclarationKind.STR_TO_INT)
          .put(Kind.STRING_ITOS, FunctionDeclarationKind.INT_TO_STR)
          .put(Kind.STRING_TO_CODE, FunctionDeclarationKind.STR_TO_CODE)
          .put(Kind.STRING_FROM_CODE, FunctionDeclarationKind.STR_FROM_CODE)
          .put(Kind.STRING_LT, FunctionDeclarationKind.STR_LT)
          .put(Kind.STRING_LEQ, FunctionDeclarationKind.STR_LE)
          .put(Kind.REGEXP_PLUS, FunctionDeclarationKind.RE_PLUS)
          .put(Kind.REGEXP_STAR, FunctionDeclarationKind.RE_STAR)
          .put(Kind.REGEXP_OPT, FunctionDeclarationKind.RE_OPTIONAL)
          .put(Kind.REGEXP_CONCAT, FunctionDeclarationKind.RE_CONCAT)
          .put(Kind.REGEXP_UNION, FunctionDeclarationKind.RE_UNION)
          .put(Kind.REGEXP_RANGE, FunctionDeclarationKind.RE_RANGE)
          .put(Kind.REGEXP_INTER, FunctionDeclarationKind.RE_INTERSECT)
          .put(Kind.REGEXP_COMPLEMENT, FunctionDeclarationKind.RE_COMPLEMENT)
          .put(Kind.REGEXP_DIFF, FunctionDeclarationKind.RE_DIFFERENCE)
          .put(Kind.SELECT, FunctionDeclarationKind.SELECT)
          .put(Kind.STORE, FunctionDeclarationKind.STORE)
          .put(Kind.STORE_ALL, FunctionDeclarationKind.CONST)
          // Separation logic
          .put(Kind.SEP_EMP, FunctionDeclarationKind.SEP_EMP)
          .put(Kind.SEP_NIL, FunctionDeclarationKind.SEP_NIL)
          .put(Kind.SEP_PTO, FunctionDeclarationKind.SEP_PTO)
          .put(Kind.SEP_STAR, FunctionDeclarationKind.SEP_STAR)
          .put(Kind.SEP_WAND, FunctionDeclarationKind.SEP_WAND)
          .buildOrThrow();

  private FunctionDeclarationKind getDeclarationKind(Expr f) {
    Kind kind = f.getKind();

    // special case: IFF for Boolean, EQ for all other types
    if (kind == Kind.EQUAL && Iterables.all(f, child -> child.getType().isBoolean())) {
      return FunctionDeclarationKind.IFF;
    }

    return KIND_MAPPING.getOrDefault(kind, FunctionDeclarationKind.OTHER);
  }

  @Override
  protected Expr getBooleanVarDeclarationImpl(Expr pTFormulaInfo) {
    Kind kind = pTFormulaInfo.getKind();
    assert kind == Kind.APPLY_UF || kind == Kind.VARIABLE : pTFormulaInfo.getKind();
    if (kind == Kind.APPLY_UF) {
      return pTFormulaInfo.getOperator();
    } else {
      return pTFormulaInfo;
    }
  }

  @Override
  public Expr callFunctionImpl(Expr pDeclaration, List<Expr> pArgs) {
    if (pArgs.isEmpty()) {
      return exprManager.mkExpr(pDeclaration);
    } else {
      vectorExpr args = new vectorExpr();
      for (Expr expr : pArgs) {
        args.add(expr);
      }
      return exprManager.mkExpr(pDeclaration, args);
    }
  }

  @Override
  public Expr declareUFImpl(String pName, Type pReturnType, List<Type> pArgTypes) {
    Expr exp = functionsCache.get(pName);
    if (exp == null) {
      vectorType args = new vectorType();
      for (Type t : pArgTypes) {
        args.add(t);
      }
      exp = exprManager.mkVar(pName, exprManager.mkFunctionType(args, pReturnType));
      functionsCache.put(pName, exp);
    } else {
      // We can't cast the cached type to FormulaType, even though it is a function type, due to a
      // bug in the CVC4 Java bindings. As a workaround we create another function type for the
      // current arguments and then compare it to the type from the cache
      vectorType args = new vectorType();
      for (Type t : pArgTypes) {
        args.add(t);
      }
      var argumentType = exprManager.mkFunctionType(args, pReturnType);
      var cachedType = exp.getType();
      Preconditions.checkArgument(
          cachedType.equals(argumentType),
          "Function %s already defined with different types or a different number of arguments",
          pName);
    }
    return exp;
  }

  @Override
  public Object convertValue(Expr expForType, Expr value) {
    final Type type = expForType.getType();
    final Type valueType = value.getType();
    if (value.getKind() == Kind.BOUND_VARIABLE) {
      // CVC4 does not allow model values for bound vars
      return value.toString();
    } else if (valueType.isBoolean()) {
      return value.getConstBoolean();

    } else if (valueType.isInteger() && type.isInteger()) {
      return new BigInteger(value.getConstRational().toString());

    } else if (valueType.isReal() && type.isReal()) {
      Rational rat = value.getConstRational();
      org.sosy_lab.common.rationals.Rational ratValue =
          org.sosy_lab.common.rationals.Rational.of(
              new BigInteger(rat.getNumerator().toString()),
              new BigInteger(rat.getDenominator().toString()));
      return ratValue.isIntegral() ? ratValue.getNum() : ratValue;

    } else if (valueType.isBitVector()) {
      Integer bv = value.getConstBitVector().getValue();
      if (bv.fitsSignedLong()) {
        return BigInteger.valueOf(bv.getUnsignedLong());
      } else {
        return value.toString(); // default
      }

    } else if (valueType.isFloatingPoint()) {
      return convertFloatingPoint(value);

    } else if (valueType.isRoundingMode()) {
      return getRoundingMode(value);

    } else if (valueType.isString()) {
      return unescapeUnicodeForSmtlib(value.getConstString().toString());

    } else {
      // String serialization for unknown terms.
      return value.toString();
    }
  }

  private FloatingPointNumber convertFloatingPoint(Expr fpExpr) {
    final var matcher = FLOATING_POINT_PATTERN.matcher(fpExpr.toString());
    if (!matcher.matches()) {
      throw new NumberFormatException("Unknown floating-point format: " + fpExpr);
    }

    final var fp = fpExpr.getConstFloatingPoint();
    final var fpType = fp.getT();
    final var expWidth = Ints.checkedCast(fpType.exponentWidth());
    // CVC4 returns the mantissa with the hidden bit, hence - 1
    final var mantWidthWithoutHiddenBit = Ints.checkedCast(fpType.significandWidth() - 1);

    final var sign = matcher.group("sign");
    final var exp = matcher.group("exp");
    final var mant = matcher.group("mant");

    Preconditions.checkArgument("1".equals(sign) || "0".equals(sign));
    Preconditions.checkArgument(exp.length() == expWidth);
    Preconditions.checkArgument(mant.length() == mantWidthWithoutHiddenBit);

    return FloatingPointNumber.of(
        Sign.of(sign.charAt(0) == '1'),
        new BigInteger(exp, 2),
        new BigInteger(mant, 2),
        getFloatingPointTypeFromSizesWithoutHiddenBit(expWidth, mantWidthWithoutHiddenBit));
  }

  @Override
  protected FloatingPointRoundingMode getRoundingMode(Expr pExpr) {
    checkArgument(
        pExpr.isConst() && pExpr.getType().isRoundingMode(),
        "Expected a constant rounding mode, but got: %s",
        pExpr);
    RoundingMode rm = pExpr.getConstRoundingMode();
    if (rm.equals(RoundingMode.roundNearestTiesToAway)) {
      return FloatingPointRoundingMode.NEAREST_TIES_AWAY;
    } else if (rm.equals(RoundingMode.roundNearestTiesToEven)) {
      return FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN;
    } else if (rm.equals(RoundingMode.roundTowardNegative)) {
      return FloatingPointRoundingMode.TOWARD_NEGATIVE;
    } else if (rm.equals(RoundingMode.roundTowardPositive)) {
      return FloatingPointRoundingMode.TOWARD_POSITIVE;
    } else if (rm.equals(RoundingMode.roundTowardZero)) {
      return FloatingPointRoundingMode.TOWARD_ZERO;
    } else {
      throw new IllegalArgumentException(
          String.format("Unknown rounding mode in Term '%s'.", pExpr));
    }
  }
}
