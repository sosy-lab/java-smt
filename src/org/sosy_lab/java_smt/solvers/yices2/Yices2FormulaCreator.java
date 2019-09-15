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


import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BOOL_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_UNINTERPRETED_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_VARIABLE;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bool_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bool_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bv_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bv_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvtype_size;
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
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_true;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_of_term;

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
    throw new IllegalArgumentException("Unknown formula type ");
  }

  @Override
  public <R> R visit(FormulaVisitor<R> pVisitor, Formula pFormula, Integer pF) {
    // TODO Auto-generated method stub
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
        return null;
      case YICES_UNINTERPRETED_TERM:
        return pVisitor.visitFreeVariable(pFormula, yices_get_term_name(pF));
      default:
        final String name = yices_get_term_name(pF);
        if (arity == 0 && name.startsWith("'")) {
          // symbols starting with "'" are missed as constants, but seen as functions of type OTHER
          return pVisitor.visitFreeVariable(pFormula, name);
        }
        ImmutableList.Builder<Formula> args = ImmutableList.builder();
        ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();
        for (int i = 0; i < arity; i++) {
          int arg = yices_term_child(pF, i);
          // TODO First child is function?
          FormulaType<?> argumentType = getFormulaType(arg);
          args.add(encapsulate(argumentType, arg));
          argTypes.add(argumentType);
        }
        // TODO name is NULL although it should not be
        return pVisitor.visitFunction(
            pFormula,
            args.build(),
            FunctionDeclarationImpl.of(
                name,
                getDeclarationKind(pF),
                argTypes.build(),
                getFormulaType(pF),
                yices_term_constructor(pF))); // decl == term_constructor?
    }
    // if (yices_term_is_arithmetic(pF)) {
    // return pVisitor.visitConstant(pFormula, convertValue(pF));
    // // check if pF is bool_const TODO replace 0 with Named variable
    // } else if (yices_term_constructor(pF) == 0) {
    // if (yices_bool_const_value(pF)) {
    // return pVisitor.visitConstant(pFormula, true);
    // } else {
    // return pVisitor.visitConstant(pFormula, false);
    // }
    // } else if (yices_)
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
      case 1:
        return null;
      default:
        return null;
    }
  }

  @Override
  public Integer callFunctionImpl(Integer pDeclaration, List<Integer> pArgs) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Integer declareUFImpl(String pName, Integer pReturnType, List<Integer> pArgTypes) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Integer getBooleanVarDeclarationImpl(Integer pTFormulaInfo) {
    // TODO Auto-generated method stub
    return null;
  }

  // TODO Pretty print type / term
  private Object parseNumeralValue(Integer pF, FormulaType<?> type) {
    if (yices_term_constructor(pF) == YICES_ARITH_CONST) {
    String value = yices_rational_const_value(pF);
    if (type.isRationalType() && value.contains("/")) {
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
      String littleEndianString = littleEndianBV.toString();
      String bigEndianString = new StringBuilder(littleEndianString).reverse().toString();
      return new BigInteger(bigEndianString);
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
      throw new IllegalArgumentException("Unexpected type: " + type);
    }
  }

}
