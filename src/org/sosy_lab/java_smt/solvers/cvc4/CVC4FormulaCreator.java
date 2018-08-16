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
package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Preconditions;
import edu.nyu.acsys.CVC4.ArrayType;
import edu.nyu.acsys.CVC4.BitVectorType;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Type;
import edu.nyu.acsys.CVC4.vectorExpr;
import edu.nyu.acsys.CVC4.vectorType;
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
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Formula.CVC4IntegerFormula;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Formula.CVC4RationalFormula;

public class CVC4FormulaCreator extends FormulaCreator<Expr, Type, CVC4Environment, Expr> {

  protected final Map<String, Expr> variablesCache = new HashMap<>();
  private final Map<String, Expr> functionsCache = new HashMap<>();
  private final ExprManager exprManager;

  protected CVC4FormulaCreator(CVC4Environment pEnvironment) {
    super(
        pEnvironment,
        pEnvironment.getExprManager().booleanType(),
        pEnvironment.getExprManager().integerType(),
        pEnvironment.getExprManager().realType());
    exprManager = pEnvironment.getExprManager();

  }

  @Override
  public Expr makeVariable(Type type, String name) {
    if (variablesCache.containsKey(name)) {
      Expr oldExp = variablesCache.get(name);
      assert type.equals(oldExp.getType());
      return oldExp;
    }

    Expr exp = exprManager.mkVar(name, type);
    variablesCache.put(name, exp);
    return exp;
  }

  protected ExprManager getExprManager() {
    return exprManager;
  }

  @Override
  public Type getBitvectorType(int pBitwidth) {
    return exprManager.mkBitVectorType(pBitwidth);
  }

  @Override
  public Type getFloatingPointType(FloatingPointType pType) {
    return exprManager.mkFloatingPointType(pType.getExponentSize(), pType.getMantissaSize());
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
    CVC4Environment env = getEnv();

    if (pFormula instanceof BitvectorFormula) {
      return (FormulaType<T>) getFormulaType(((CVC4BitvectorFormula) pFormula).getTerm());
    }
    // TODO: handle ArrayFormula (and FloatingPointFormula)
    // (HINT: look at corresponding method in MathSat5 part)
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
      return FormulaType.getBitvectorTypeWithSize((int) (new BitVectorType(t)).getSize());
    } else if (t.isFloatingPoint()) {
      return FormulaType.getFloatingPointType(
          (int) ((edu.nyu.acsys.CVC4.FloatingPointType) t).getExponentSize(),
          (int) ((edu.nyu.acsys.CVC4.FloatingPointType) t).getSignificandSize());
    } else if (t.isReal()) {
      // The theory REAL in CVC4 is the theory of (infinite precision!) real numbers.
      // As such, the theory RATIONAL is contained in REAL. TODO: find a better solution.
      return FormulaType.RationalType;
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
            "Trying to encapsulate formula of type %s as %s", getFormulaType(pTerm), pType);
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
    }
    throw new IllegalArgumentException("Cannot create formulas of type " + pType + " in MathSAT");
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

  private String getName(Expr pT) {
    Preconditions.checkState(!pT.isNull());

    if (pT.isConst() || pT.isVariable()) {
      return dequote(pT.toString());
    } else {
      return dequote(pT.getOperator().toString());
    }
  }

  /*
  private Expr replaceArgs(Expr pT, List<Expr> pNewArgs) {
    // TODO!
    throw new UnsupportedOperationException("Not implemented");
  }
  */

  /**
   * Variable names can be wrapped with "|". This function removes those chars. I copied it from
   * SMTInterpolFormulaCreator. TODO: remove code duplication
   */
  private String dequote(String s) {
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
      } else if (type.isInteger() || type.isFloatingPoint()) {
        return visitor.visitConstant(formula, f.getConstRational());
      } else if (type.isBitVector()) {
        // TODO is this correct?
        return visitor.visitConstant(formula, f.getConstBitVector().getValue());
      } else {
        throw new UnsupportedOperationException("Unhandled constant kind");
      }

    } else if (f.isVariable()) {
      return visitor.visitFreeVariable(formula, getName(f));

    } else {
      // Expressions like uninterpreted function calls (Kind.APPLY_UF) or operators (e.g. Kind.AND).
      // These are all treated like operators, so we can get the declaration by f.getOperator()!
      String name = getName(f);
      long arity = f.getNumChildren();

      List<Formula> args = new ArrayList<>((int) arity);
      List<FormulaType<?>> argsTypes = new ArrayList<>((int) arity);
      for (int i = 0; i < arity; i++) {
        Expr arg = f.getChild(i);
        FormulaType<?> argType = getFormulaType(arg);
        args.add(encapsulateWithTypeOf(arg));
        argsTypes.add(argType);
      }

      return visitor.visitFunction(
          formula,
          args,
          FunctionDeclarationImpl.of(
              name, getDeclarationKind(f), argsTypes, getFormulaType(f), f.getOperator()));
    }
  }

  private FunctionDeclarationKind getDeclarationKind(Expr f) {
    Kind kind = f.getKind();
    // see src/theory/*/kinds in CVC4 sources for description of the different CVC4 kinds ;)
    if (kind == Kind.EQUAL) {
      return FunctionDeclarationKind.EQ;
    } else if (kind == Kind.DISTINCT) {
      return FunctionDeclarationKind.DISTINCT;
    } else if (kind == Kind.NOT) {
      return FunctionDeclarationKind.NOT;
    } else if (kind == Kind.AND) {
      return FunctionDeclarationKind.AND;
    } else if (kind == Kind.EQUAL) {
      return FunctionDeclarationKind.IFF;
    } else if (kind == Kind.IMPLIES) {
      return FunctionDeclarationKind.IMPLIES;
    } else if (kind == Kind.OR) {
      return FunctionDeclarationKind.OR;
    } else if (kind == Kind.XOR) {
      return FunctionDeclarationKind.XOR;
    } else if (kind == Kind.ITE) {
      return FunctionDeclarationKind.ITE;
    } else if (kind == Kind.APPLY_UF) {
      return FunctionDeclarationKind.UF;
    } else if (kind == Kind.PLUS) {
      return FunctionDeclarationKind.ADD;
    } else if (kind == Kind.MULT) {
      return FunctionDeclarationKind.MUL;
    } else if (kind == Kind.MINUS) {
      return FunctionDeclarationKind.SUB;
    } else if (kind == Kind.DIVISION) {
      return FunctionDeclarationKind.DIV;
    } else if (kind == Kind.LT) {
      return FunctionDeclarationKind.LT;
    } else if (kind == Kind.LEQ) {
      return FunctionDeclarationKind.LTE;
    } else if (kind == Kind.GT) {
      return FunctionDeclarationKind.GT;
    } else if (kind == Kind.GEQ) {
      return FunctionDeclarationKind.GTE;
    } else if (kind == Kind.BITVECTOR_PLUS) {
      return FunctionDeclarationKind.BV_ADD;
    } else if (kind == Kind.BITVECTOR_SUB) {
      return FunctionDeclarationKind.BV_SUB;
    } else if (kind == Kind.BITVECTOR_MULT) {
      return FunctionDeclarationKind.BV_MUL;
    } else if (kind == Kind.BITVECTOR_AND) {
      return FunctionDeclarationKind.BV_AND;
    } else if (kind == Kind.BITVECTOR_OR) {
      return FunctionDeclarationKind.BV_OR;
    } else if (kind == Kind.BITVECTOR_XOR) {
      return FunctionDeclarationKind.BV_XOR;
    } else if (kind == Kind.BITVECTOR_SLT) {
      return FunctionDeclarationKind.BV_SLT;
    } else if (kind == Kind.BITVECTOR_ULT) {
      return FunctionDeclarationKind.BV_ULT;
    } else if (kind == Kind.BITVECTOR_SLE) {
      return FunctionDeclarationKind.BV_SLE;
    } else if (kind == Kind.BITVECTOR_ULE) {
      return FunctionDeclarationKind.BV_ULE;
    } else if (kind == Kind.BITVECTOR_SGT) {
      return FunctionDeclarationKind.BV_SGT;
    } else if (kind == Kind.BITVECTOR_UGT) {
      return FunctionDeclarationKind.BV_UGT;
    } else if (kind == Kind.BITVECTOR_SGE) {
      return FunctionDeclarationKind.BV_SGE;
    } else if (kind == Kind.BITVECTOR_UGE) {
      return FunctionDeclarationKind.BV_UGE;
    } else if (kind == Kind.BITVECTOR_SDIV) {
      return FunctionDeclarationKind.BV_SDIV;
    } else if (kind == Kind.BITVECTOR_UDIV) {
      return FunctionDeclarationKind.BV_UDIV;
    } else if (kind == Kind.BITVECTOR_SREM) {
      // TODO: find out where Kind.BITVECTOR_SMOD fits in here
      return FunctionDeclarationKind.BV_SREM;
    } else if (kind == Kind.BITVECTOR_UREM) {
      return FunctionDeclarationKind.BV_UREM;
    } else if (kind == Kind.BITVECTOR_NOT) {
      return FunctionDeclarationKind.BV_NOT;
    } else if (kind == Kind.BITVECTOR_NEG) {
      return FunctionDeclarationKind.BV_NEG;
    } else if (kind == Kind.BITVECTOR_EXTRACT) {
      return FunctionDeclarationKind.BV_EXTRACT;
    } else if (kind == Kind.BITVECTOR_CONCAT) {
      return FunctionDeclarationKind.BV_CONCAT;
    } else {
      return FunctionDeclarationKind.OTHER;
    }
  }

  @Override
  protected Expr getBooleanVarDeclarationImpl(Expr pTFormulaInfo) {
    Kind kind = pTFormulaInfo.getKind();
    assert (kind == Kind.APPLY_UF || kind == Kind.VARIABLE) : pTFormulaInfo.getKind();
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
    if (!functionsCache.containsKey(pName)) {
      vectorType args = new vectorType();
      for (Type t : pArgTypes) {
        args.add(t);
      }
      Type requestedFunctionType = exprManager.mkFunctionType(args, pReturnType);
      Expr result = exprManager.mkVar(pName, requestedFunctionType);
      functionsCache.put(pName, result);
      return result;
    } else {
      return functionsCache.get(pName);
    }
  }
}
