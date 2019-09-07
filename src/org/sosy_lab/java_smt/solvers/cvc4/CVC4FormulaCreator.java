/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.cvc4;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import edu.nyu.acsys.CVC4.ArrayType;
import edu.nyu.acsys.CVC4.BitVectorType;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Integer;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Rational;
import edu.nyu.acsys.CVC4.Type;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.acsys.CVC4.vectorType;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
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

public class CVC4FormulaCreator extends FormulaCreator<Expr, Type, ExprManager, Expr> {

  private final Map<String, Expr> variablesCache = new HashMap<>();
  private final Map<String, Expr> functionsCache = new HashMap<>();
  private final ExprManager exprManager;

  protected CVC4FormulaCreator(ExprManager pExprManager) {
    super(
        pExprManager,
        pExprManager.booleanType(),
        pExprManager.integerType(),
        pExprManager.realType());
    exprManager = pExprManager;
  }

  @Override
  public Expr makeVariable(Type type, String name) {
    Expr exp = variablesCache.computeIfAbsent(name, n -> exprManager.mkVar(name, type));
    assert type.equals(exp.getType());
    return exp;
  }

  @Override
  public Type getBitvectorType(int pBitwidth) {
    return exprManager.mkBitVectorType(pBitwidth);
  }

  @Override
  public Type getFloatingPointType(FloatingPointType pType) {
    return exprManager.mkFloatingPointType(
        pType.getExponentSize(), pType.getMantissaSize() + 1); // plus sign bit
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
  protected <TD extends Formula, TR extends Formula> FormulaType<TR> getArrayFormulaElementType(
      ArrayFormula<TD, TR> pArray) {
    return ((CVC4ArrayFormula<TD, TR>) pArray).getElementType();
  }

  @Override
  protected <TD extends Formula, TR extends Formula> FormulaType<TD> getArrayFormulaIndexType(
      ArrayFormula<TD, TR> pArray) {
    return ((CVC4ArrayFormula<TD, TR>) pArray).getIndexType();
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    Type t = extractInfo(pFormula).getType();
    if (pFormula instanceof BitvectorFormula) {
      checkArgument(t.isBitVector(), "BitvectorFormula with actual type " + t + ": " + pFormula);
      return (FormulaType<T>) getFormulaType(extractInfo(pFormula));

    } else if (pFormula instanceof FloatingPointFormula) {
      checkArgument(
          t.isFloatingPoint(), "FloatingPointFormula with actual type " + t + ": " + pFormula);
      edu.nyu.acsys.CVC4.FloatingPointType fpType = new edu.nyu.acsys.CVC4.FloatingPointType(t);
      return (FormulaType<T>)
          FormulaType.getFloatingPointType(
              (int) fpType.getExponentSize(),
              (int) fpType.getSignificandSize() - 1); // without sign bit

    } else if (pFormula instanceof ArrayFormula<?, ?>) {
      FormulaType<T> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<T, T>) pFormula);
      FormulaType<T> arrayElementType = getArrayFormulaElementType((ArrayFormula<T, T>) pFormula);
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    }
    return super.getFormulaType(pFormula);
  }

  @Override
  public FormulaType<?> getFormulaType(Expr pFormula) {
    Type t = pFormula.getType();

    if (t.isArray()) {
      // it can happen that t is instance of Type but not instance of ArrayType! But this workaround
      // seems to work:
      ArrayType arrayType = new ArrayType(t);
      return FormulaType.getArrayType(
          getFormulaTypeFromTermType(arrayType.getIndexType()),
          getFormulaTypeFromTermType(arrayType.getConstituentType()));
    }
    return getFormulaTypeFromTermType(t);
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
      edu.nyu.acsys.CVC4.FloatingPointType fpType = new edu.nyu.acsys.CVC4.FloatingPointType(t);
      return FormulaType.getFloatingPointType(
          (int) fpType.getExponentSize(),
          (int) fpType.getSignificandSize() - 1); // without sign bit
    } else if (t.isRoundingMode()) {
      return FormulaType.FloatingPointRoundingModeType;
    } else if (t.isReal()) {
      // The theory REAL in CVC4 is the theory of (infinite precision!) real numbers.
      // As such, the theory RATIONAL is contained in REAL. TODO: find a better solution.
      return FormulaType.RationalType;
    } else if (t.isArray()) {
      ArrayType arrayType = new ArrayType(t); // instead of casting, create a new type.
      Type indexType = arrayType.getIndexType();
      Type elementType = arrayType.getConstituentType();
      return FormulaType.getArrayType(
          getFormulaTypeFromTermType(indexType), getFormulaTypeFromTermType(elementType));
    } else {
      throw new AssertionError("Unhandled type " + t.getBaseType());
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
    }
    throw new IllegalArgumentException("Cannot create formulas of type " + pType + " in CVC4");
  }

  @Override
  public BooleanFormula encapsulateBoolean(Expr pTerm) {
    assert getFormulaType(pTerm).isBooleanType();
    return new CVC4BooleanFormula(pTerm);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Expr pTerm) {
    assert getFormulaType(pTerm).isBitvectorType();
    return new CVC4BitvectorFormula(pTerm);
  }

  @Override
  protected FloatingPointFormula encapsulateFloatingPoint(Expr pTerm) {
    assert getFormulaType(pTerm).isFloatingPointType();
    return new CVC4FloatingPointFormula(pTerm);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      Expr pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType));
    return new CVC4ArrayFormula<>(pTerm, pIndexType, pElementType);
  }

  private static String getName(Expr e) {
    Preconditions.checkState(!e.isNull());
    if (!e.isConst() && !e.isVariable()) {
      e = e.getOperator();
    }
    return dequote(e.toString());
  }

  /** Variable names can be wrapped with "|". This function removes those chars. */
  private static String dequote(String s) {
    int l = s.length();
    if (s.charAt(0) == '|' && s.charAt(l - 1) == '|') {
      return s.substring(1, l - 1);
    }
    return s;
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, final Expr f) {
    Preconditions.checkState(!f.isNull());

    Type type = f.getType();

    if (f.isConst()) {
      if (type.isBoolean()) {
        return visitor.visitConstant(formula, f.getConstBoolean());
      } else if (type.isInteger() || type.isReal()) {
        return visitor.visitConstant(formula, f.getConstRational());
      } else if (type.isBitVector()) {
        // TODO is this correct?
        return visitor.visitConstant(formula, f.getConstBitVector().getValue());
      } else if (type.isFloatingPoint()) {
        // TODO is this correct?
        return visitor.visitConstant(formula, f.getConstFloatingPoint());
      } else if (type.isRoundingMode()) {
        // TODO is this correct?
        return visitor.visitConstant(formula, f.getConstRoundingMode());
      } else {
        throw new UnsupportedOperationException("Unhandled constant " + f + " with type " + type);
      }

    } else if (f.isVariable()) {
      return visitor.visitFreeVariable(formula, getName(f));

    } else {
      // Expressions like uninterpreted function calls (Kind.APPLY_UF) or operators (e.g. Kind.AND).
      // These are all treated like operators, so we can get the declaration by f.getOperator()!
      List<Formula> args = new ArrayList<>();
      List<FormulaType<?>> argsTypes = new ArrayList<>();
      for (Expr arg : f) {
        FormulaType<?> argType = getFormulaType(arg);
        args.add(encapsulateWithTypeOf(arg));
        argsTypes.add(argType);
      }

      return visitor.visitFunction(
          formula,
          args,
          FunctionDeclarationImpl.of(
              getName(f), getDeclarationKind(f), argsTypes, getFormulaType(f), f.getOperator()));
    }
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
          .put(Kind.DIVISION, FunctionDeclarationKind.DIV)
          .put(Kind.LT, FunctionDeclarationKind.LT)
          .put(Kind.LEQ, FunctionDeclarationKind.LTE)
          .put(Kind.GT, FunctionDeclarationKind.GT)
          .put(Kind.GEQ, FunctionDeclarationKind.GTE)
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
          // TODO: find out where Kind.BITVECTOR_SMOD fits in here
          .put(Kind.BITVECTOR_UREM, FunctionDeclarationKind.BV_UREM)
          .put(Kind.BITVECTOR_NOT, FunctionDeclarationKind.BV_NOT)
          .put(Kind.BITVECTOR_NEG, FunctionDeclarationKind.BV_NEG)
          .put(Kind.BITVECTOR_EXTRACT, FunctionDeclarationKind.BV_EXTRACT)
          .put(Kind.BITVECTOR_CONCAT, FunctionDeclarationKind.BV_CONCAT)
          .put(Kind.TO_INTEGER, FunctionDeclarationKind.FLOOR)
          .build();

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
    if (pArgs.size() == 0) {
      return exprManager.mkExpr(Kind.APPLY_UF, pDeclaration);
    } else if (pArgs.size() == 1) {
      return exprManager.mkExpr(Kind.APPLY_UF, pDeclaration, pArgs.get(0));
    } else {
      vectorExpr args = new vectorExpr();
      for (Expr expr : pArgs) {
        args.add(expr);
      }
      return exprManager.mkExpr(Kind.APPLY_UF, pDeclaration, args);
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
    }
    return exp;
  }

  @Override
  public Object convertValue(Expr pF) {
    throw new UnsupportedOperationException(
        "CVC4 needs a second term to determine a correct type. Please use the other method.");
  }

  @Override
  public Object convertValue(Expr expForType, Expr value) {
    final Type type = expForType.getType();
    if (value.getType().isBoolean()) {
      return value.getConstBoolean();

    } else if (value.getType().isInteger() && type.isInteger()) {
      return new BigInteger(value.getConstRational().toString());

    } else if (value.getType().isReal() && type.isReal()) {
      Rational rat = value.getConstRational();
      return org.sosy_lab.common.rationals.Rational.of(
          new BigInteger(rat.getNumerator().toString()),
          new BigInteger(rat.getDenominator().toString()));

    } else if (value.getType().isBitVector()) {
      Integer bv = value.getConstBitVector().getValue();
      if (bv.fitsSignedLong()) {
        return BigInteger.valueOf(bv.getUnsignedLong());
      } else {
        return value.toString(); // default
      }

    } else if (value.getType().isFloatingPoint()) {
      Rational rat = value.getConstFloatingPoint().convertToRationalTotal(new Rational(0));
      return org.sosy_lab.common.rationals.Rational.of(
          new BigInteger(rat.getNumerator().toString()),
          new BigInteger(rat.getDenominator().toString()));

    } else {
      // String serialization for unknown terms.
      return value.toString();
    }
  }
}
