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

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ABS;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_AND;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_APP_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_GE_ATOM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ARITH_SUM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BIT_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BOOL_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_ARRAY;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_ASHR;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_CONST;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_DIV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_GE_ATOM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_LSHR;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_REM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SDIV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SGE_ATOM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SHL;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SMOD;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SREM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_BV_SUM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_CEIL;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_DISTINCT_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_DIVIDES_ATOM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_EQ_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_FLOOR;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_IDIV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_IMOD;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_IS_INT_ATOM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_ITE_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_NOT_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_OR_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_POWER_PRODUCT;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_RDIV;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_SELECT_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_UNINTERPRETED_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_VARIABLE;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_XOR_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_abs;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_and;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_application;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_arith_geq_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bool_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bool_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bv_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bv_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvarray;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvashr;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvconst_from_array;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvdiv;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvge_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvlshr;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvrem;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsdiv;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsge_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvshl;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsmod;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsrem;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsum;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvsum_component;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvtype_size;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_ceil;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_distinct;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_divides_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_division;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_eq;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_false;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_floor;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_function_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_get_term_name;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_idiv;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_imod;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_int_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_is_int_atom;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_ite;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_mul;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_named_variable;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_not;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_or;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_rational;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_product;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_product_component;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_proj_arg;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_proj_index;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_rational_const_value;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_real_type;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_sum;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_sum_component;
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
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_is_bitvector;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_of_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_xor;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.Collections2;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.primitives.Ints;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
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
    super(env, yices_bool_type(), yices_int_type(), yices_real_type());
  }

  @Override
  public Integer getBitvectorType(int pBitwidth) {
    return yices_bv_type(pBitwidth);
  }

  @Override
  public Integer getFloatingPointType(FloatingPointType pType) {
    throw new UnsupportedOperationException();
  }

  @Override
  public Integer getArrayType(Integer pIndexType, Integer pElementType) {
    throw new UnsupportedOperationException();
  }

  @Override
  public Integer makeVariable(Integer pType, String pVarName) {
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
                && getFormulaType(pTerm).equals(FormulaType.IntegerType))
        : String.format(
            "Trying to encapsulate formula %s of type %s as %s",
            yices_term_to_string(pTerm), getFormulaType(pTerm), pType);
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
    } else if (yices_term_is_real(pFormula)) {
      return FormulaType.RationalType;
    } else if (yices_term_is_bitvector(pFormula)) {
      return FormulaType.getBitvectorTypeWithSize(yices_term_bitsize(pFormula));
    }
    throw new IllegalArgumentException(
        String.format(
            "Unknown formula type '%s' for formula '%s'",
            yices_type_to_string(yices_type_of_term(pFormula)), yices_term_to_string(pFormula)));
  }

  @Override
  public <R> R visit(FormulaVisitor<R> pVisitor, Formula pFormula, Integer pF) {
    int constructor = yices_term_constructor(pF);
    switch (constructor) {
      case YICES_BOOL_CONST:
        return pVisitor.visitConstant(pFormula, yices_bool_const_value(pF));
      case YICES_ARITH_CONST:
        return pVisitor.visitConstant(pFormula, convertValue(pF, pF));
      case YICES_BV_CONST:
        return pVisitor.visitConstant(pFormula, convertValue(pF, pF));
      case YICES_UNINTERPRETED_TERM:
        return pVisitor.visitFreeVariable(pFormula, yices_get_term_name(pF));
      default:
        return visitFunctionApplication(pVisitor, pFormula, pF, constructor);
    }
  }

  private <R> R visitFunctionApplication(
      FormulaVisitor<R> pVisitor, Formula pFormula, int pF, final int constructor) {
    final FunctionDeclarationKind kind = getDeclarationKind(pF, constructor);
    final ImmutableList.Builder<Formula> args = ImmutableList.builder();
    final ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();

    // Map built-in constructors in negative int to avoid collision with UFs.
    int functionDeclaration = -constructor;

    List<Integer> yicesArgs = null;
    String name = kind.toString();
    switch (kind) {
      case UF:
        yicesArgs = getArgs(pF);
        name = yices_term_to_string(yicesArgs.get(0));
        functionDeclaration = yicesArgs.get(0);
        yicesArgs.remove(0);
        break;
      case ADD:
        yicesArgs = getSumArgs(pF);
        break;
      case BV_ADD:
        yicesArgs = getBvSumArgs(pF);
        break;
      case BV_NOT:
        yicesArgs = getBvArgs(pF, kind, 1);
        break;
      case BV_EQ:
      case BV_AND:
      case BV_OR:
      case BV_XOR:
        yicesArgs = getBvArgs(pF, kind, 2);
        break;
      case MUL:
      case BV_MUL:
        switch (constructor) {
          case YICES_ARITH_SUM:
            yicesArgs = getMultiplySumArgsFromSum(pF);
            functionDeclaration = -YICES_POWER_PRODUCT;
            break;
          case YICES_POWER_PRODUCT:
            yicesArgs = getMultiplyArgs(pF);
            break;
          default:
            throw new AssertionError("unhandled multiplication: " + yices_term_to_string(pF));
        }
        break;
      case BV_SIGN_EXTENSION:
      case BV_ZERO_EXTENSION:
        yicesArgs = ImmutableList.of(getExtendArg(pF));
        break;
      case BV_EXTRACT:
        yicesArgs = ImmutableList.of(getExtractArg(pF));
        break;
      case BV_CONCAT:
        yicesArgs = getConcatArgs(pF);
        break;
      default:
        // special case for AND
        if (kind == FunctionDeclarationKind.AND && isNestedConjunction(pF)) {
          name = FunctionDeclarationKind.AND.toString();
          functionDeclaration = -YICES_AND; // Workaround for unavailable Yices_AND constructor.
          yicesArgs = getNestedConjunctionArgs(pF);
        } else {
          yicesArgs = getArgs(pF);
        }
    }
    for (int arg : yicesArgs) {
      FormulaType<?> argumentType = getFormulaType(arg);
      args.add(encapsulate(argumentType, arg));
      argTypes.add(argumentType);
    }

    return pVisitor.visitFunction(
        pFormula,
        args.build(),
        FunctionDeclarationImpl.of(
            name, kind, argTypes.build(), getFormulaType(pF), functionDeclaration));
  }

  /** get the kind of function from the first (or more) array elements. */
  private static FunctionDeclarationKind getArrayKind(int array) {
    Preconditions.checkArgument(YICES_BV_ARRAY == yices_term_constructor(array));
    Preconditions.checkArgument(yices_term_num_children(array) > 0);

    // get all constructors
    List<Integer> constructors = new ArrayList<>();
    for (int child : getArgs(array)) {
      constructors.add(yices_term_constructor(child));
    }

    // if all constructors are equal, we can use them directly
    if (ImmutableSet.copyOf(constructors).size() == 1) {
      int constructor = constructors.get(0);
      switch (constructor) {
        case YICES_EQ_TERM:
          return FunctionDeclarationKind.BV_EQ;
        case YICES_NOT_TERM:
          if (Iterables.all(getArgs(array), Yices2FormulaCreator::isNestedConjunction)) {
            return FunctionDeclarationKind.BV_AND;
          } else {
            return FunctionDeclarationKind.BV_NOT;
          }
        case YICES_OR_TERM:
          return FunctionDeclarationKind.BV_OR;
        case YICES_XOR_TERM:
          return FunctionDeclarationKind.BV_XOR;
      }
    }

    // check for EXTRACT: incrementing sequence of indices
    if (isExtractOperation(array)) {
      return FunctionDeclarationKind.BV_EXTRACT;
    }

    // check for CONCAT: several ARGs in sequence
    if (isConcatOperation(array)) {
      return FunctionDeclarationKind.BV_CONCAT;
    }

    { // check for EXPAND: initial bits are identical, either FALSE or HIGHEST_BIT
      int highestChild = yices_term_child(array, yices_term_num_children(array) - 1);
      int equalPrefix = 0;
      for (int i = yices_term_num_children(array) - 2; i >= 0; i--) {
        equalPrefix++;
        if (highestChild != yices_term_child(array, i)) {
          break;
        }
      }
      // if we found a sequence of equal terms, if original size is smaller than current term
      if (equalPrefix > 1) {
        if (highestChild == yices_false()) {
          return FunctionDeclarationKind.BV_ZERO_EXTENSION;
        } else {
          return FunctionDeclarationKind.BV_SIGN_EXTENSION;
        }
      }
    }

    // otherwise we do not know
    return FunctionDeclarationKind.OTHER;
  }

  private static boolean isExtractOperation(final int array) {
    int firstChild = yices_term_child(array, 0);
    if (yices_term_constructor(firstChild) != YICES_BIT_TERM) {
      return false;
    }
    List<Integer> indizes = new ArrayList<>();
    final int arg = yices_proj_arg(firstChild);
    for (int child : getArgs(array)) {
      if (yices_term_constructor(child) == YICES_BIT_TERM) {
        int index = yices_proj_index(child);
        if (arg == yices_proj_arg(child)
            && (indizes.isEmpty() || Iterables.getLast(indizes) == index - 1)) {
          indizes.add(index);
        } else {
          return false;
        }
      } else {
        return false;
      }
    }
    return true;
  }

  private static boolean isConcatOperation(final int array) {
    List<Integer> args = new ArrayList<>();
    for (int child : getArgs(array)) {
      if (yices_term_constructor(child) == YICES_BIT_TERM) {
        int arg = yices_proj_arg(child);
        if (args.isEmpty() || Iterables.getLast(args) != arg) {
          args.add(arg);
        } else {
          continue;
        }
      } else {
        return false;
      }
    }
    return args.size() > 1; // concat needs more than one element
  }

  private static FunctionDeclarationKind getDeclarationKind(int pF, final int constructor) {
    List<Integer> constantsAndVariables =
        ImmutableList.of(
            YICES_BOOL_CONST,
            YICES_ARITH_CONST,
            YICES_BV_CONST,
            YICES_VARIABLE,
            YICES_UNINTERPRETED_TERM);
    assert !constantsAndVariables.contains(constructor)
        : String.format(
            "Term %s with constructor %d should be handled somewhere else",
            yices_term_to_string(pF), constructor);

    switch (constructor) {
      case YICES_ITE_TERM:
        return FunctionDeclarationKind.ITE;
      case YICES_APP_TERM:
        return FunctionDeclarationKind.UF;
      case YICES_EQ_TERM:
        return FunctionDeclarationKind.EQ; // Covers all equivalences
      case YICES_DISTINCT_TERM:
        return FunctionDeclarationKind.DISTINCT;
      case YICES_NOT_TERM:
        if (isNestedConjunction(pF)) {
          return FunctionDeclarationKind.AND;
        } else {
          return FunctionDeclarationKind.NOT;
        }
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
        return FunctionDeclarationKind.DIV;
      case YICES_SELECT_TERM:
        return FunctionDeclarationKind.SELECT;
      case YICES_BV_SUM:
        return FunctionDeclarationKind.BV_ADD;
      case YICES_ARITH_SUM:
        if (yices_term_num_children(pF) == 1) {
          return FunctionDeclarationKind.MUL;
        }
        return FunctionDeclarationKind.ADD;
      case YICES_POWER_PRODUCT:
        if (yices_type_is_bitvector(yices_type_of_term(pF))) {
          return FunctionDeclarationKind.BV_MUL;
        } else {
          return FunctionDeclarationKind.MUL;
        }
      case YICES_BV_ARRAY:
        return getArrayKind(pF);

      default:
        if (constructor == YICES_BIT_TERM) {
          // TODO Visit bit(t i) in meaningful way
        }
        return FunctionDeclarationKind.OTHER;
    }
  }

  /** Yices transforms <code>AND(x,...)</code> into <code>NOT(OR(NOT(X),NOT(...))</code>. */
  private static boolean isNestedConjunction(int outerTerm) {
    if (yices_term_constructor(outerTerm) != YICES_NOT_TERM) {
      return false;
    }

    int middleTerm = yices_term_child(outerTerm, 0);
    if (yices_term_constructor(middleTerm) != YICES_OR_TERM) {
      return false;
    }

    // code commented out --> ignore nested NOTs and just negate all resulting child-terms.
    // for (int child : getArgs(middleTerm)) {
    //   if (yices_term_constructor(child) != YICES_NOT_TERM) {
    //     return false;
    //   }
    // }

    return true;
  }

  /**
   * Yices transforms <code>AND(x,...)</code> into <code>NOT(OR(NOT(X),NOT(...))</code>.
   *
   * <p>Only call this method for terms that are nested conjunctions!
   */
  private static List<Integer> getNestedConjunctionArgs(int outerTerm) {
    Preconditions.checkArgument(yices_term_constructor(outerTerm) == YICES_NOT_TERM);
    int middleTerm = yices_term_child(outerTerm, 0);
    Preconditions.checkArgument(yices_term_constructor(middleTerm) == YICES_OR_TERM);
    List<Integer> result = new ArrayList<>();
    for (int child : getArgs(middleTerm)) {
      result.add(yices_not(child));
    }
    return result;
  }

  private static List<Integer> getArgs(int parent) {
    List<Integer> children = new ArrayList<>();
    for (int i = 0; i < yices_term_num_children(parent); i++) {
      children.add(yices_term_child(parent, i));
    }
    return children;
  }

  private static List<Integer> getSumArgs(int parent) {
    List<Integer> children = new ArrayList<>();
    for (int i = 0; i < yices_term_num_children(parent); i++) {
      String[] child = yices_sum_component(parent, i);
      String coeff = child[0];
      int term = Integer.parseInt(child[1]);
      if (term == -1) { // No term just a number
        children.add(yices_parse_rational(coeff));
      } else { // return only term / ignores coefficient
        int coeffTerm = yices_parse_rational(coeff);
        children.add(yices_mul(coeffTerm, term));
      }
    }
    return children;
  }

  private static List<Integer> getBvSumArgs(int parent) {
    List<Integer> children = new ArrayList<>();
    int bitsize = yices_term_bitsize(parent);
    for (int i = 0; i < yices_term_num_children(parent); i++) {
      int[] component = yices_bvsum_component(parent, i, bitsize);
      if (component[component.length - 1] == -1) { // No term
        children.add(yices_bvconst_from_array(bitsize, Arrays.copyOfRange(component, 0, bitsize)));
      } else { // return only term / ignores coefficient
        children.add(component[component.length - 1]);
      }
    }
    return children;
  }

  /** extract -1 and X from the sum of one element [-1*x]. */
  private static List<Integer> getMultiplySumArgsFromSum(int parent) {
    Preconditions.checkArgument(yices_term_num_children(parent) == 1);
    String[] child = yices_sum_component(parent, 0);
    int term = Integer.parseInt(child[1]);
    Preconditions.checkArgument(term != -1, "unexpected constant coeff without variable");
    int coeffTerm = yices_parse_rational(child[0]);
    return ImmutableList.of(coeffTerm, term);
  }

  private static List<Integer> getMultiplyArgs(int parent) {
    List<Integer> result = new ArrayList<>();
    for (int i = 0; i < yices_term_num_children(parent); i++) {
      int[] component = yices_product_component(parent, i);
      result.add(component[0]); // add term ignore exponent
    }
    return result;
  }

  /** remove the identical prefix from the given bitvector. */
  private static Integer getExtendArg(int parent) {
    List<Integer> result = new ArrayList<>();
    boolean takeRest = false;
    Integer highestBit = null;
    for (int child : Lists.reverse(getArgs(parent))) {
      if (highestBit == null) {
        highestBit = child;
      }
      if (takeRest) {
        result.add(child);
      } else if (highestBit == child) {
        continue;
      } else {
        takeRest = true;
        if (highestBit != yices_false()) {
          result.add(highestBit);
        }
        result.add(child);
      }
    }
    return collapse(Lists.reverse(result));
  }

  /** get the "X" from "(extract fromHigh toLow X)". */
  private static int getExtractArg(int parent) {
    int firstChild = yices_term_child(parent, 0);
    return yices_proj_arg(firstChild);
  }

  /** get the "X", "Y", and "Z" from "(concat X Y Z)". */
  private static List<Integer> getConcatArgs(int parent) {
    Set<Integer> result = new LinkedHashSet<>(); // ordering is important!
    for (int child : getArgs(parent)) {
      result.add(yices_proj_arg(child));
    }
    return ImmutableList.copyOf(result);
  }

  /** convert from [OP(x1,y1),OP(x2,y2),...] to [x1,x2,...] and [y1,y2,...]. */
  private static List<Integer> getBvArgs(
      int parent, FunctionDeclarationKind kind, int numberOfArgs) {
    List<List<Integer>> args = new ArrayList<>();
    for (int ai = 0; ai < numberOfArgs; ai++) {
      args.add(new ArrayList<>());
    }
    for (int i = 0; i < yices_term_num_children(parent); i++) {
      int child = yices_term_child(parent, i);
      List<Integer> children;
      if (FunctionDeclarationKind.BV_AND == kind) {
        children = getNestedConjunctionArgs(child);
      } else {
        children = getArgs(child);
      }
      for (int ai = 0; ai < numberOfArgs; ai++) {
        args.get(ai).add(children.get(ai));
      }
    }
    return Lists.transform(args, Yices2FormulaCreator::collapse);
  }

  private static int collapse(List<Integer> bits) {
    return yices_bvarray(bits.size(), Ints.toArray(bits));
  }

  @Override
  public Integer callFunctionImpl(Integer pDeclaration, List<Integer> pArgs) {
    if (pDeclaration < 0) { // is constant function application from API
      switch (-pDeclaration) {
        case YICES_ITE_TERM:
          checkArgsLength("YICES_ITE_TERM", pArgs, 3);
          return yices_ite(pArgs.get(0), pArgs.get(1), pArgs.get(2));
        case YICES_EQ_TERM:
          checkArgsLength("YICES_EQ_TERM", pArgs, 2);
          return yices_eq(pArgs.get(0), pArgs.get(1));
        case YICES_DISTINCT_TERM:
          return yices_distinct(pArgs.size(), Ints.toArray(pArgs));
        case YICES_NOT_TERM:
          checkArgsLength("YICES_NOT_TERM", pArgs, 1);
          return yices_not(pArgs.get(0));
        case YICES_OR_TERM:
          return yices_or(pArgs.size(), Ints.toArray(pArgs));
        case YICES_XOR_TERM:
          return yices_xor(pArgs.size(), Ints.toArray(pArgs));
        case YICES_BV_DIV:
          checkArgsLength("YICES_BV_DIV", pArgs, 2);
          return yices_bvdiv(pArgs.get(0), pArgs.get(1));
        case YICES_BV_REM:
          checkArgsLength("YICES_BV_REM", pArgs, 2);
          return yices_bvrem(pArgs.get(0), pArgs.get(1));
        case YICES_BV_SDIV:
          checkArgsLength("YICES_BV_SDIV", pArgs, 2);
          return yices_bvsdiv(pArgs.get(0), pArgs.get(1));
        case YICES_BV_SREM:
          checkArgsLength("YICES_BV_SREM", pArgs, 2);
          return yices_bvsrem(pArgs.get(0), pArgs.get(1));
        case YICES_BV_SMOD:
          checkArgsLength("YICES_BV_SMOD", pArgs, 2);
          return yices_bvsmod(pArgs.get(0), pArgs.get(1));
        case YICES_BV_SHL:
          checkArgsLength("YICES_BV_SHL", pArgs, 2);
          return yices_bvshl(pArgs.get(0), pArgs.get(1));
        case YICES_BV_LSHR:
          checkArgsLength("YICES_BV_LSHR", pArgs, 2);
          return yices_bvlshr(pArgs.get(0), pArgs.get(1));
        case YICES_BV_ASHR:
          checkArgsLength("YICES_BV_ASHR", pArgs, 2);
          return yices_bvashr(pArgs.get(0), pArgs.get(1));
        case YICES_BV_GE_ATOM:
          checkArgsLength("YICES_BV_GE_ATOM", pArgs, 2);
          return yices_bvge_atom(pArgs.get(0), pArgs.get(1));
        case YICES_BV_SGE_ATOM:
          checkArgsLength("YICES_BV_SGE_ATOM", pArgs, 2);
          return yices_bvsge_atom(pArgs.get(0), pArgs.get(1));
        case YICES_ARITH_GE_ATOM:
          checkArgsLength("YICES_ARITH_GE_ATOM", pArgs, 2);
          return yices_arith_geq_atom(pArgs.get(0), pArgs.get(1));
        case YICES_ABS:
          checkArgsLength("YICES_ABS", pArgs, 1);
          return yices_abs(pArgs.get(0));
        case YICES_CEIL:
          checkArgsLength("YICES_CEIL", pArgs, 1);
          return yices_ceil(pArgs.get(0));
        case YICES_FLOOR:
          checkArgsLength("YICES_FLOOR", pArgs, 1);
          return yices_floor(pArgs.get(0));
        case YICES_RDIV:
          checkArgsLength("YICES_RDIV", pArgs, 2);
          return yices_division(pArgs.get(0), pArgs.get(1));
        case YICES_IDIV:
          checkArgsLength("YICES_IDIV", pArgs, 2);
          return yices_idiv(pArgs.get(0), pArgs.get(1));
        case YICES_IMOD:
          checkArgsLength("YICES_IMOD", pArgs, 2);
          return yices_imod(pArgs.get(0), pArgs.get(1));
        case YICES_IS_INT_ATOM:
          checkArgsLength("YICES_IS_INT_ATOM", pArgs, 1);
          return yices_is_int_atom(pArgs.get(0));
        case YICES_DIVIDES_ATOM:
          checkArgsLength("YICES_DIVIDES_ATOM", pArgs, 2);
          return yices_divides_atom(pArgs.get(0), pArgs.get(1));
        case YICES_BV_SUM:
          return yices_bvsum(pArgs.size(), Ints.toArray(pArgs));
        case YICES_ARITH_SUM:
          return yices_sum(pArgs.size(), Ints.toArray(pArgs));
        case YICES_POWER_PRODUCT:
          return yices_product(pArgs.size(), Ints.toArray(pArgs));
        case YICES_AND: // Workaround for missing and constructor
          return yices_and(pArgs.size(), Ints.toArray(pArgs));
          // TODO add more cases
        default:
          throw new IllegalArgumentException(
              "Unknown function declaration with constant value " + -pDeclaration);
      }
    } else { // is UF Application
      int size = pArgs.size();
      if (size == 0) {
        return pDeclaration;
      } else {
        int[] argArray = Ints.toArray(pArgs);
        int app = yices_application(pDeclaration, size, argArray);
        return app;
      }
    }
  }

  private void checkArgsLength(String kind, List<Integer> pArgs, final int expectedLength) {
    Preconditions.checkArgument(
        pArgs.size() == expectedLength,
        "%s with %s expected arguments was called with unexpected arguments: %s",
        kind,
        expectedLength,
        Collections2.transform(pArgs, a -> yices_term_to_string(a)));
  }

  @Override
  public Integer declareUFImpl(String pName, Integer pReturnType, List<Integer> pArgTypes) {
    int size = pArgTypes.size();
    int[] argTypeArray = Ints.toArray(pArgTypes);
    final int yicesFuncType;
    if (pArgTypes.isEmpty()) {
      // a nullary function is a plain symbol (variable)
      yicesFuncType = pReturnType;
    } else {
      yicesFuncType = yices_function_type(size, argTypeArray, pReturnType);
    }
    int uf = yices_named_variable(yicesFuncType, pName);
    return uf;
  }

  @Override
  protected Integer getBooleanVarDeclarationImpl(Integer pTFormulaInfo) {
    return yices_term_constructor(pTFormulaInfo);
  }

  private Object parseNumeralValue(Integer pF, FormulaType<?> type) {
    if (yices_term_constructor(pF) == YICES_ARITH_CONST) {
      String value = yices_rational_const_value(pF);
      if (type.isRationalType()) {
        return Rational.of(value);
      } else if (type.isIntegerType()) {
        return new BigInteger(value);
      } else {
        throw new IllegalArgumentException("Unexpected type: " + type);
      }
    } else {
      throw new IllegalArgumentException(
          String.format(
              "Term: '%s' with type '%s' is not an arithmetic constant",
              yices_term_to_string(pF), yices_type_to_string(yices_type_of_term(pF))));
    }
  }

  private BigInteger parseBitvector(int pF) {
    if (yices_term_constructor(pF) == YICES_BV_CONST) {
      int[] littleEndianBV = yices_bv_const_value(pF, yices_term_bitsize(pF));
      Preconditions.checkArgument(littleEndianBV.length != 0, "BV was empty");
      String bigEndianBV = Joiner.on("").join(Lists.reverse(Ints.asList(littleEndianBV)));
      return new BigInteger(bigEndianBV, 2);
    } else {
      throw new IllegalArgumentException(
          String.format("Term: '%s' is not a bitvector constant", yices_term_to_string(pF)));
    }
  }

  @Override
  public Object convertValue(Integer key) {
    throw new UnsupportedOperationException(
        "Yices needs a second term to determine a correct type. Please use the other method.");
  }

  @Override
  public Object convertValue(Integer typeKey, Integer pF) {
    FormulaType<?> type = getFormulaType(typeKey);
    if (type.isBooleanType()) {
      return pF.equals(yices_true());
    } else if (type.isRationalType() || type.isIntegerType()) {
      return parseNumeralValue(pF, type);
    } else if (type.isBitvectorType()) {
      return parseBitvector(pF);
    } else {
      throw new IllegalArgumentException(
          "Unexpected type: " + yices_type_to_string(yices_type_of_term(pF)));
    }
  }
}
