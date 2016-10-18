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

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

import edu.nyu.acsys.CVC4.ArrayType;
import edu.nyu.acsys.CVC4.BitVectorType;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Type;

import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Formula.CVC4BooleanFormula;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Formula.CVC4IntegerFormula;

import java.util.ArrayList;
import java.util.List;

public class CVC4FormulaCreator extends FormulaCreator<Expr, Type, CVC4Environment, Expr> {

  private final ExprManager exprManager;

  protected CVC4FormulaCreator(CVC4Environment pEnv) {
    super(pEnv, pEnv.getExprManager().booleanType(), pEnv.getExprManager().integerType(), null);
    exprManager = pEnv.getExprManager();
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
  public Expr makeVariable(Type pType, String pVarName) {
    return exprManager.mkVar(pVarName, pType);
  }

  @Override
  public Expr extractInfo(Formula pT) {
    return CVC4FormulaManager.getCVC4Expr(pT);
  }

  @Override
  public FormulaType<?> getFormulaType(Expr pFormula) {
    Type t = pFormula.getType();
    if (t.isArray()) {
      return FormulaType.getArrayType(
          getFormulaTypeFromTermType(((ArrayType) t).getIndexType()),
          getFormulaTypeFromTermType(t.getBaseType()));
    }
    return getFormulaTypeFromTermType(t);
  }

  private FormulaType<?> getFormulaTypeFromTermType(Type t) {
    if (t.isBoolean()) {
      return FormulaType.BooleanType;
    } else if (t.isInteger()) {
      return FormulaType.IntegerType;
    } else if (t.isBitVector()) {
      return FormulaType.getBitvectorTypeWithSize((int) ((BitVectorType) t).getSize());
    } else if (t.isFloatingPoint()) {
      return FormulaType.getFloatingPointType(
          (int) ((edu.nyu.acsys.CVC4.FloatingPointType) t).getExponentSize(),
          (int) ((edu.nyu.acsys.CVC4.FloatingPointType) t).getSignificandSize());
    } else {
      throw new AssertionError("Unhandled type " + t.getClass());
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
    } else {
      throw new IllegalArgumentException("Cannot create formulas of type " + pType + " in MathSAT");
    }
  }

  @Override
  public BooleanFormula encapsulateBoolean(Expr pTerm) {
    assert getFormulaType(pTerm).isBooleanType();
    return new CVC4BooleanFormula(pTerm);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Expr pTerm) {
    return null;
  }

  @Override
  protected FloatingPointFormula encapsulateFloatingPoint(Expr pTerm) {
    return null;
  }

  @Override
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      Expr pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType));
    return null;
  }

  private String getName(Expr pT) {
    Preconditions.checkState(!pT.isNull());

    if (pT.isConst() || pT.isVariable()) {
      return pT.toString();
    } else {
      return pT.getOperator().toString();
    }
  }

  private Expr replaceArgs(Expr pT, List<Expr> pNewArgs) {
    throw new UnsupportedOperationException("Not implemented");
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
        return visitor.visitConstant(formula, f.getConstBitVector().getValue());
      } else {
        throw new UnsupportedOperationException("Unhandled constant kind");
      }

    } else if (f.isVariable()) {
      return visitor.visitFreeVariable(formula, f.toString());

    } else {
      String name = getName(f);
      long arity = f.getNumChildren();
      ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();

      List<Formula> args = new ArrayList<>((int) arity);
      for (int i = 0; i < arity; i++) {
        Expr arg = f.getChild(i);
        args.add(encapsulateWithTypeOf(arg));
        argTypes.add(getFormulaType(arg));
      }

      Function<List<Formula>, Formula> constructor =
          new Function<List<Formula>, Formula>() {
            @Override
            public Formula apply(List<Formula> formulas) {
              return encapsulateWithTypeOf(replaceArgs(f, extractInfo(formulas)));
            }
          };
      return visitor.visitFunction(
          formula, args, FunctionDeclarationImpl.of(name, getDeclarationKind(f), argTypes.build(), getFormulaType(f), 1));

    }
  }

  private FunctionDeclarationKind getDeclarationKind(Expr f) {
    Kind kind = f.getKind();
    if (kind == Kind.EQUAL) {
      return FunctionDeclarationKind.EQ;
    } else if (kind == Kind.DISTINCT) {
      return FunctionDeclarationKind.DISTINCT;
    } else if (kind == Kind.NOT) {
      return FunctionDeclarationKind.NOT;
    } else if (kind == Kind.AND) {
      return FunctionDeclarationKind.AND;
    } else if (kind == Kind.IFF) {
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
    } else {
      return FunctionDeclarationKind.OTHER;
    }
  }

  @Override
  public Expr callFunctionImpl(FunctionDeclarationImpl<?, Expr> pDeclaration, List<Expr> pArgs) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr getBooleanVarDeclarationImpl(Expr pTFormulaInfo) {
    // TODO Auto-generated method stub
    return null;
  }
}
