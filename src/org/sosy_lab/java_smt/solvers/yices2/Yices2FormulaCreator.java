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
package org.sosy_lab.java_smt.solvers.yices2;


import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_APP_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_GE_ATOM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_SUM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BOOL_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_ASHR;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_DIV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_GE_ATOM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_LSHR;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_REM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SDIV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SGE_ATOM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SHL;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SREM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SUM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_DISTINCT_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_EQ_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_FLOOR;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_IDIV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ITE_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_NOT_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_OR_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_POWER_PRODUCT;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_RDIV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_SELECT_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_UNINTERPRETED_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_VARIABLE;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_XOR_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_application;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bool_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bool_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bv_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bv_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvtype_size;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_function_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_term_name;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_named_variable;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_rational_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_real_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_bitsize;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_child;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_constructor;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_is_bitvector;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_is_bool;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_is_int;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_is_real;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_num_children;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_true;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_of_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_to_string;

import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.yices2.Yices2Formula.Yices2BitvectorFormula;
import org.sosy_lab.java_smt.solvers.yices2.Yices2Formula.Yices2BooleanFormula;
import org.sosy_lab.java_smt.solvers.yices2.Yices2Formula.Yices2IntegerFormula;
import org.sosy_lab.java_smt.solvers.yices2.Yices2Formula.Yices2RationalFormula;

public class Yices2FormulaCreator extends FormulaCreator<Integer, Integer, Long, Integer> {


  protected Yices2FormulaCreator(long env) {
    super(
        env,
        yices_bool_type(),
        yices_int_type(),
        yices_real_type());
  }

  @Override
  public Integer getBitvectorType(int pBitwidth) {
    return yices_bv_type(pBitwidth);
  }

  @Override
  public Integer getFloatingPointType(FloatingPointType pType) {
    // TODO Yices has no floatingPointType
    return null;
  }

  @Override
  public Integer getArrayType(Integer pIndexType, Integer pElementType) {
    // TODO Yices has no arrayType?
    return null;
  }

  @Override
  public Integer makeVariable(Integer pType, String pVarName) {
    // TODO Use yices_uninterpreted_term for variable making?
    return yices_named_variable(pType, pVarName);
  }

  @Override
  public Integer extractInfo(Formula pT) {
    return Yices2FormulaManager.getYicesTerm(pT);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, Integer pTerm) {
    assert pType.equals(getFormulaType(pTerm))
        || (pType.equals(FormulaType.RationalType)
            && getFormulaType(pTerm).equals(FormulaType.IntegerType)) : String.format(
                "Trying to encapsulate formula of type %s as %s",
                getFormulaType(pTerm),
                pType);
    if (pType.isBooleanType()) {
      return (T) new Yices2BooleanFormula(pTerm);
    } else if (pType.isIntegerType()) {
      return (T) new Yices2IntegerFormula(pTerm);
    } else if (pType.isRationalType()) {
      return (T) new Yices2RationalFormula(pTerm);
    } else if (pType.isBitvectorType()) {
      return (T) new Yices2BitvectorFormula(pTerm);
    }
    throw new IllegalArgumentException("Cannot create formulas of type " + pType + " in Yices");
  }

  @Override
  public BooleanFormula encapsulateBoolean(Integer pTerm) {
    assert getFormulaType(pTerm).isBooleanType();
    return new Yices2BooleanFormula(pTerm);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Integer pTerm) {
    assert getFormulaType(pTerm).isBitvectorType();
    return new Yices2BitvectorFormula(pTerm);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    if (pFormula instanceof BitvectorFormula) {
      int type = yices_type_of_term(extractInfo(pFormula));
      // checkArgument(
      // yices_is_bitvector(type),
      // "BitvectorFormula with actual type " + msat_type_repr(type) + ": " + pFormula);
      return (FormulaType<T>) FormulaType.getBitvectorTypeWithSize(yices_bvtype_size(type));
    } else {
      return super.getFormulaType(pFormula);
    }
  }

  @Override
  public FormulaType<?> getFormulaType(Integer pFormula) {
    if (yices_term_is_bool(pFormula)) {
      return FormulaType.BooleanType;
    } else if (yices_term_is_int(pFormula)) {
      return FormulaType.IntegerType;
      // TODO is_real correct?
    } else if (yices_term_is_real(pFormula)) {
      return FormulaType.RationalType;
    } else if (yices_term_is_bitvector(pFormula)) {
      return FormulaType.getBitvectorTypeWithSize(yices_term_bitsize(pFormula));
    }
    // TODO add type info
    throw new IllegalArgumentException(
        "Unknown formula type: " + yices_type_to_string(yices_type_of_term(pFormula), 100, 10, 0));
  }

  @Override
  public <R> R visit(FormulaVisitor<R> pVisitor, Formula pFormula, Integer pF) {
    // TODO Auto-generated method stub
    System.out.println(yices_term_to_string(pF, 100, 10, 0));
    int arity = yices_term_num_children(pF);
    int constructor = yices_term_constructor(pF);
    switch (constructor) {
      case YICES_BOOL_CONST:
        if (yices_bool_const_value(pF)) {
          return pVisitor.visitConstant(pFormula, true);
        } else {
          return pVisitor.visitConstant(pFormula, false);
        }
      case YICES_ARITH_CONST:
        return pVisitor.visitConstant(pFormula, convertValue(pF));
      case YICES_BV_CONST:
        // TODO Implement BV Value
        return pVisitor.visitConstant(pFormula, convertValue(pF));
      case YICES_UNINTERPRETED_TERM:
        return pVisitor.visitFreeVariable(pFormula, yices_get_term_name(pF));
      default:
        String name = yices_get_term_name(pF);
        // TODO
        FunctionDeclarationKind kind = getDeclarationKind(pF);
        if (name == null) {
          if (kind.toString() != null) {
            name = kind.toString();
          } else {
            throw new NullPointerException("FunctionDeclarationKind.toString() was NULL");
          }
        }
        System.out.println("Parent: " + name);
        ImmutableList.Builder<Formula> args = ImmutableList.builder();
        ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();
        int i = 0;
        // if(kind == FunctionDeclarationKind.UF) {
        // int fun = yices_term_child(pF, 0);
        // name = yices_get_term_name(fun);
        // i = 1;
        // }
        for (; i < arity; i++) {
          int arg = yices_term_child(pF, i);
          System.out.println("?????????");
          System.out.println("Child: " + yices_term_to_string(arg, 100, 10, 0));
          System.out.println("?????????");
          FormulaType<?> argumentType = getFormulaType(arg);
          args.add(encapsulate(argumentType, arg));
          argTypes.add(argumentType);
        }
        return pVisitor.visitFunction(
            pFormula,
            args.build(),
            FunctionDeclarationImpl.of(
                name,
                kind,
                argTypes.build(),
                getFormulaType(pF),
                yices_term_constructor(pF))); // decl == term_constructor?
    }
  }

  private FunctionDeclarationKind getDeclarationKind(int pF) {
    // TODO If uninterpreted function
    List<Integer> constantsAndVariables =
        ImmutableList.of(
            YICES_BOOL_CONST,
            YICES_ARITH_CONST,
            YICES_BV_CONST,
            YICES_VARIABLE,
            YICES_UNINTERPRETED_TERM);
    int constructor = yices_term_constructor(pF);
    assert !constantsAndVariables
        .contains(constructor) : "Variables should be handled somewhere else";

    switch (constructor) {
      case YICES_ITE_TERM:
        return FunctionDeclarationKind.ITE;
      case YICES_APP_TERM:
        return FunctionDeclarationKind.UF; // TODO correct?
      case YICES_EQ_TERM:
        return FunctionDeclarationKind.EQ; // Covers all equivalences
      case YICES_DISTINCT_TERM:
        return FunctionDeclarationKind.DISTINCT;
      case YICES_NOT_TERM:
        return FunctionDeclarationKind.NOT;
      case YICES_OR_TERM:
        return FunctionDeclarationKind.OR;
      case YICES_XOR_TERM:
        return FunctionDeclarationKind.XOR;
      case YICES_BV_DIV:
        return FunctionDeclarationKind.BV_UDIV;
      case YICES_BV_REM:
        return FunctionDeclarationKind.BV_UREM;
      case YICES_BV_SDIV:
        return FunctionDeclarationKind.BV_SDIV;
      case YICES_BV_SREM:
        return FunctionDeclarationKind.BV_SREM;
      case YICES_BV_SHL:
        return FunctionDeclarationKind.BV_SHL;
      case YICES_BV_LSHR:
        return FunctionDeclarationKind.BV_LSHR;
      case YICES_BV_ASHR:
        return FunctionDeclarationKind.BV_ASHR;
      case YICES_BV_GE_ATOM:
        return FunctionDeclarationKind.BV_UGE;
      case YICES_BV_SGE_ATOM:
        return FunctionDeclarationKind.BV_SGE;
      case YICES_ARITH_GE_ATOM:
        return FunctionDeclarationKind.GTE;
      case YICES_FLOOR:
        return FunctionDeclarationKind.FLOOR;
      case YICES_RDIV:
        return FunctionDeclarationKind.DIV;
      case YICES_IDIV:
        return FunctionDeclarationKind.DIV; // correct?
      case YICES_SELECT_TERM:
        return FunctionDeclarationKind.SELECT;
      case YICES_BV_SUM:
        return FunctionDeclarationKind.BV_ADD;
      case YICES_ARITH_SUM:
        return FunctionDeclarationKind.ADD;
      case YICES_POWER_PRODUCT:
        return FunctionDeclarationKind.MUL;

      default:
        System.out.println("Encountered term constructor:" + constructor);
        return FunctionDeclarationKind.OTHER;
    }
  }

  @Override
  public Integer callFunctionImpl(Integer pDeclaration, List<Integer> pArgs) {
    // TODO Auto-generated method stub
    System.out.println("----------");
    System.out.println(yices_term_to_string(pDeclaration, 100, 10, 0));
    System.out
        .println("Type: " + yices_type_to_string(yices_type_of_term(pDeclaration), 100, 10, 0));
    int size = pArgs.size();
    int[] argArray = new int[size];
    for (int i = 0; i < size; i++) {
      argArray[i] = pArgs.get(i);
      System.out.println(yices_term_to_string(argArray[i], 100, 10, 0));
    }
    System.out.println("----------");
    int app = yices_application(pDeclaration, size, argArray);
    System.out.println("APP" + yices_term_to_string(app, 100, 10, 0));
    return app;
  }

  @Override
  public Integer declareUFImpl(String pName, Integer pReturnType, List<Integer> pArgTypes) {
    // TODO Auto-generated method stub
    int size = pArgTypes.size();
    int[] argTypeArray = new int[size];
    for (int i = 0; i < size; i++) {
      argTypeArray[i] = pArgTypes.get(i);
    }
    final int yicesFuncType;
    if (pArgTypes.isEmpty()) {
      // a nullary function is a plain symbol (variable)
      yicesFuncType = pReturnType;
    } else {
      yicesFuncType = yices_function_type(size, argTypeArray, pReturnType);
    }
    return yices_named_variable(yicesFuncType, pName);
  }

  @Override
  protected Integer getBooleanVarDeclarationImpl(Integer pTFormulaInfo) {
    // TODO Unsure what to return here
    return null;
  }

  // TODO Pretty print type / term
  private Object parseNumeralValue(Integer pF, FormulaType<?> type) {
    if (yices_term_constructor(pF) == YICES_ARITH_CONST) {
      String value = yices_rational_const_value(pF);
      if (type.isRationalType()) {
        return Rational.of(value);
      } else if (type.isIntegerType() && !value.contains("/")) {
        return new BigInteger(value);
      } else {
        throw new IllegalArgumentException("Unexpected type: " + type);
      }
    } else {
      throw new IllegalArgumentException("Term: " + pF + " is not an arithmetic constant");
    }
  }

  private BigInteger parseBitvector(Integer pF) {
    if (yices_term_constructor(pF) == YICES_BV_CONST) {
      int[] littleEndianBV = yices_bv_const_value(pF, yices_term_bitsize(pF));
      String bigEndianBV = "";
      for (int i = littleEndianBV.length - 1; i >= 0; i--) {
        bigEndianBV = bigEndianBV + littleEndianBV[i];
      }
      if (bigEndianBV != "") {
        return new BigInteger(bigEndianBV, 2);
      } else {
        throw new IllegalArgumentException("BV was empty");
      }
    } else {
      throw new IllegalArgumentException("Term: " + pF + " is not a bitvector constant");
    }
  }

  // TODO Pretty print type
  @Override
  public Object convertValue(Integer pF) {
    // TODO Auto-generated method stub
    FormulaType<?> type = getFormulaType(pF);
    if (type.isBooleanType()) {
      return pF.equals(yices_true());
    } else if (type.isRationalType() || type.isIntegerType()) {
      return parseNumeralValue(pF, type);
    } else if (type.isBitvectorType()) {
      return parseBitvector(pF);
    } else {
      throw new IllegalArgumentException(
          "Unexpected type: " + yices_type_to_string(yices_type_of_term(pF), 100, 1, 0));
    }
  }

}
