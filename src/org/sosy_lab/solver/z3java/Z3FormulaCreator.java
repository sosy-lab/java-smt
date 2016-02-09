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
package org.sosy_lab.solver.z3java;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Table;
import com.microsoft.z3.ArraySort;
import com.microsoft.z3.BitVecSort;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntSymbol;
import com.microsoft.z3.Sort;
import com.microsoft.z3.StringSymbol;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.enumerations.Z3_ast_kind;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import com.microsoft.z3.enumerations.Z3_sort_kind;

import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.solver.api.ArrayFormula;
import org.sosy_lab.solver.api.BitvectorFormula;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.FunctionDeclarationKind;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.solver.basicimpl.FormulaCreator;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

class Z3FormulaCreator extends FormulaCreator<Expr, Sort, Context> {

  private final Table<Sort, Sort, Sort> allocatedArraySorts = HashBasedTable.create();

  Z3FormulaCreator(
      Context pEnv, Sort pBoolType, Sort pIntegerType, Sort pRealType, Configuration config) {
    super(pEnv, pBoolType, pIntegerType, pRealType);
  }

  @Override
  public Expr makeVariable(Sort type, String varName) {
    Context z3context = getEnv();
    StringSymbol symbol = z3context.mkSymbol(varName);
    return z3context.mkConst(symbol, type);
  }

  @Override
  public Expr extractInfo(Formula pT) {
    // for visibility
    return super.extractInfo(pT);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    if (pFormula instanceof ArrayFormula<?, ?> || pFormula instanceof BitvectorFormula) {
      Expr term = extractInfo(pFormula);
      return (FormulaType<T>) getFormulaType(term);
    }

    return super.getFormulaType(pFormula);
  }

  public FormulaType<?> getFormulaTypeFromSort(Sort pSort) {
    switch (pSort.getSortKind()) {
      case Z3_BOOL_SORT:
        return FormulaType.BooleanType;
      case Z3_INT_SORT:
        return FormulaType.IntegerType;
      case Z3_REAL_SORT:
        return FormulaType.RationalType;
      case Z3_ARRAY_SORT:
        Preconditions.checkArgument(pSort instanceof ArraySort);
        ArraySort aSort = (ArraySort) pSort;
        return FormulaType.getArrayType(
            getFormulaTypeFromSort(aSort.getDomain()), getFormulaTypeFromSort(aSort.getRange()));
      case Z3_BV_SORT:
        Preconditions.checkArgument(pSort instanceof BitVecSort);
        return FormulaType.getBitvectorTypeWithSize(((BitVecSort) pSort).getSize());
      default:
        throw new IllegalArgumentException("Unknown formula type");
    }
  }

  @Override
  public FormulaType<?> getFormulaType(Expr pFormula) {
    return getFormulaTypeFromSort(pFormula.getSort());
  }

  @Override
  public Sort getArrayType(Sort pIndexType, Sort pElementType) {
    Sort allocatedArraySort = allocatedArraySorts.get(pIndexType, pElementType);
    if (allocatedArraySort == null) {
      allocatedArraySort = getEnv().mkArraySort(pIndexType, pElementType);
      allocatedArraySorts.put(pIndexType, pElementType, allocatedArraySort);
    }
    return allocatedArraySort;
  }

  @Override
  public Sort getBitvectorType(int pBitwidth) {
    checkArgument(pBitwidth > 0, "Cannot use bitvector type with size %s", pBitwidth);
    return getEnv().mkBitVecSort(pBitwidth);
  }

  @Override
  public Sort getFloatingPointType(FormulaType.FloatingPointType type) {
    throw new UnsupportedOperationException("FloatingPoint theory is not supported by Z3");
  }

  private String getName(Expr t) {
    Z3_ast_kind astKind = t.getASTKind();
    if (astKind == Z3_ast_kind.Z3_VAR_AST) {
      return "?" + t.getIndex();
    } else {
      FuncDecl funcDecl = t.getFuncDecl();
      Symbol symbol = funcDecl.getName();
      if (symbol instanceof IntSymbol) {
        return Integer.toString(((IntSymbol) symbol).getInt());
      } else if (symbol instanceof StringSymbol) {
        return ((StringSymbol) symbol).getString();
      } else {
        throw new AssertionError();
      }
    }
  }

  private Expr replaceArgs(Expr t, List<Expr> newArgs) {
    Preconditions.checkState(t.getNumArgs() == newArgs.size());
    Expr[] newParams = newArgs.toArray(new Expr[] {});
    // TODO check equality of sort of each oldArg and newArg
    return environment.mkApp(t.getFuncDecl(), newParams);
  }

  @Override
  @SuppressWarnings("unchecked")
  public <R> R visit(FormulaVisitor<R> visitor, final Formula formula, final Expr f) {
    switch (f.getASTKind()) {
      case Z3_NUMERAL_AST:
        return visitor.visitConstant(formula, convertValue(f));
      case Z3_APP_AST:
        String name = getName(f);
        int arity = f.getNumArgs();

        if (arity == 0) {

          // true/false.
          Z3_decl_kind declKind = f.getFuncDecl().getDeclKind();
          if (declKind == Z3_decl_kind.Z3_OP_TRUE || declKind == Z3_decl_kind.Z3_OP_FALSE) {
            return visitor.visitConstant(formula, declKind == Z3_decl_kind.Z3_OP_TRUE);
          } else {

            // Has to be a variable otherwise.
            // TODO: assert that.
            return visitor.visitFreeVariable(formula, name);
          }
        }

        List<Formula> args = new ArrayList<>(arity);
        for (int i = 0; i < arity; i++) {
          Expr arg = f.getArgs()[i];
          FormulaType<?> argumentType = getFormulaType(arg);
          args.add(encapsulate(argumentType, arg));
        }

        // Any function application.
        Function<List<Formula>, Formula> constructor =
            new Function<List<Formula>, Formula>() {
              @Override
              public Formula apply(List<Formula> formulas) {
                return encapsulateWithTypeOf(replaceArgs(f, extractInfo(formulas)));
              }
            };
        return visitor.visitFunction(
            formula, args, FunctionDeclaration.of(name, getDeclarationKind(f)), constructor);
      case Z3_VAR_AST:
        int deBruijnIdx = f.getIndex();
        return visitor.visitBoundVariable(formula, deBruijnIdx);
      case Z3_QUANTIFIER_AST:
        Preconditions.checkArgument(f instanceof com.microsoft.z3.Quantifier);
        com.microsoft.z3.Quantifier qf = (com.microsoft.z3.Quantifier) f;
        BooleanFormula body = encapsulateBoolean(qf.getBody());
        Quantifier q = qf.isUniversal() ? Quantifier.FORALL : Quantifier.EXISTS;
        return visitor.visitQuantifier((BooleanFormula) formula, q, getBoundVars(qf), body);

      case Z3_SORT_AST:
      case Z3_FUNC_DECL_AST:
      case Z3_UNKNOWN_AST:
      default:
        throw new UnsupportedOperationException(
            "Input should be a formula AST, " + "got unexpected type instead");
    }
  }

  private List<Formula> getBoundVars(com.microsoft.z3.Quantifier pQf) {
    int numBound = pQf.getNumBound();
    List<Formula> boundVars = new ArrayList<>(numBound);
    Symbol[] varNames = pQf.getBoundVariableNames();
    Sort[] varSorts = pQf.getBoundVariableSorts();
    for (int i = 0; i < numBound; i++) {
      boundVars.add(
          encapsulate(
              getFormulaTypeFromSort(varSorts[i]), environment.mkConst(varNames[i], varSorts[i])));
    }
    return boundVars;
  }

  private FunctionDeclarationKind getDeclarationKind(Expr pF) {
    Z3_decl_kind decl = pF.getFuncDecl().getDeclKind();

    if (pF.getArgs().length == 0) {
      return FunctionDeclarationKind.VAR;
    }

    switch (decl) {
      case Z3_OP_AND:
        return FunctionDeclarationKind.AND;
      case Z3_OP_NOT:
        return FunctionDeclarationKind.NOT;
      case Z3_OP_OR:
        return FunctionDeclarationKind.OR;
      case Z3_OP_IFF:
        return FunctionDeclarationKind.IFF;
      case Z3_OP_ITE:
        return FunctionDeclarationKind.ITE;
      case Z3_OP_XOR:
        return FunctionDeclarationKind.XOR;
      case Z3_OP_DISTINCT:
        return FunctionDeclarationKind.DISTINCT;
      case Z3_OP_IMPLIES:
        return FunctionDeclarationKind.IMPLIES;

      case Z3_OP_SUB:
        return FunctionDeclarationKind.SUB;
      case Z3_OP_ADD:
        return FunctionDeclarationKind.ADD;
      case Z3_OP_DIV:
        return FunctionDeclarationKind.DIV;
      case Z3_OP_MUL:
        return FunctionDeclarationKind.MUL;
      case Z3_OP_MOD:
        return FunctionDeclarationKind.MODULO;

      case Z3_OP_UNINTERPRETED:
        return FunctionDeclarationKind.UF;

      case Z3_OP_LT:
        return FunctionDeclarationKind.LT;
      case Z3_OP_LE:
        return FunctionDeclarationKind.LTE;
      case Z3_OP_GT:
        return FunctionDeclarationKind.GT;
      case Z3_OP_GE:
        return FunctionDeclarationKind.GTE;
      case Z3_OP_EQ:
        return FunctionDeclarationKind.EQ;

      default:
        return FunctionDeclarationKind.OTHER;
    }
  }

  public Object convertValue(Expr pF) {
    FormulaType<?> type = getFormulaType(pF);
    if (type.isBooleanType()) {
      return pF.isTrue();
    } else if (type.isIntegerType()) {
      return new BigInteger(pF.toString());
    } else if (type.isRationalType()) {

      // String serialization is expensive, but getting arbitrary-sized
      // numbers is difficult otherwise.
      // TODO: an optimization is possible here, try to get an integer first,
      // resort to strings if that fails.
      return Rational.ofString(pF.toString());
    } else if (type.isBitvectorType()) {
      return interpretBitvector(pF);
    } else {

      // Unknown type --- return string serialization.
      return pF.toString();
    }
  }

  private static BigInteger interpretBitvector(Expr pF) {
    Sort argSort = pF.getSort();
    Z3_sort_kind sortKind = argSort.getSortKind();
    Preconditions.checkArgument(sortKind == Z3_sort_kind.Z3_BV_SORT);
    return new BigInteger(pF.toString());
  }
}
