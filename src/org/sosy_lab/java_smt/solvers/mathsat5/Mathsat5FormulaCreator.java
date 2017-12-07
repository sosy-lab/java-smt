/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.mathsat5;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_AND;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_ARRAY_READ;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_ARRAY_WRITE;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_ADD;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_AND;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_ASHR;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_CONCAT;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_EXTRACT;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_LSHL;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_LSHR;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_MUL;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_NEG;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_NOT;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_OR;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_SDIV;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_SLE;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_SLT;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_SREM;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_SUB;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_UDIV;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_ULE;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_ULT;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_UREM;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_BV_XOR;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_EQ;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_FP_ADD;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_FP_DIV;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_FP_EQ;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_FP_LE;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_FP_LT;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_FP_MUL;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_FP_NEG;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_FP_ROUND_TO_INT;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_FP_SUB;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_IFF;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_ITE;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_LEQ;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_NOT;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_OR;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_PLUS;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.MSAT_TAG_UNKNOWN;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_decl_get_name;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_decl_get_tag;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_declare_function;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_array_element_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_array_index_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_array_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_bool_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_bv_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_bv_type_size;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_fp_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_fp_type_exp_width;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_fp_type_mant_width;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_integer_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_rational_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_is_array_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_is_bool_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_is_bv_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_is_fp_roundingmode_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_is_fp_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_is_integer_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_is_rational_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_constant;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_term;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_arity;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_arg;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_decl;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_is_constant;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_is_false;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_is_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_is_true;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_is_uf;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_repr;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_type_repr;

import com.google.common.collect.ImmutableList;
import com.google.common.primitives.Longs;
import com.google.common.primitives.UnsignedInteger;
import com.google.common.primitives.UnsignedLong;
import java.math.BigInteger;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.sosy_lab.common.rationals.Rational;
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
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5Formula.Mathsat5ArrayFormula;
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5Formula.Mathsat5BitvectorFormula;
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5Formula.Mathsat5BooleanFormula;
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5Formula.Mathsat5FloatingPointFormula;
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5Formula.Mathsat5FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5Formula.Mathsat5IntegerFormula;
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5Formula.Mathsat5RationalFormula;

class Mathsat5FormulaCreator extends FormulaCreator<Long, Long, Long, Long> {

  private static final Pattern FLOATING_POINT_PATTERN = Pattern.compile("^(\\d+)_(\\d+)_(\\d+)$");
  private static final Pattern BITVECTOR_PATTERN = Pattern.compile("^(\\d+)_(\\d+)$");

  Mathsat5FormulaCreator(final Long msatEnv) {
    super(
        msatEnv,
        msat_get_bool_type(msatEnv),
        msat_get_integer_type(msatEnv),
        msat_get_rational_type(msatEnv));
  }

  @Override
  public Long makeVariable(Long type, String varName) {
    long funcDecl = msat_declare_function(getEnv(), varName, type);
    return msat_make_constant(getEnv(), funcDecl);
  }

  @Override
  public Long extractInfo(Formula pT) {
    return Mathsat5FormulaManager.getMsatTerm(pT);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    long env = getEnv();
    if (pFormula instanceof BitvectorFormula) {
      long type = msat_term_get_type(extractInfo(pFormula));
      checkArgument(
          msat_is_bv_type(env, type),
          "BitvectorFormula with actual type " + msat_type_repr(type) + ": " + pFormula);
      return (FormulaType<T>)
          FormulaType.getBitvectorTypeWithSize(msat_get_bv_type_size(env, type));

    } else if (pFormula instanceof FloatingPointFormula) {
      long type = msat_term_get_type(extractInfo(pFormula));
      checkArgument(
          msat_is_fp_type(env, type),
          "FloatingPointFormula with actual type " + msat_type_repr(type) + ": " + pFormula);
      return (FormulaType<T>)
          FormulaType.getFloatingPointType(
              msat_get_fp_type_exp_width(env, type), msat_get_fp_type_mant_width(env, type));
    } else if (pFormula instanceof ArrayFormula<?, ?>) {
      FormulaType<T> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<T, T>) pFormula);
      FormulaType<T> arrayElementType = getArrayFormulaElementType((ArrayFormula<T, T>) pFormula);
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    }
    return super.getFormulaType(pFormula);
  }

  @Override
  public FormulaType<?> getFormulaType(Long pFormula) {
    long type = msat_term_get_type(pFormula);
    return getFormulaTypeFromTermType(type);
  }

  private FormulaType<?> getFormulaTypeFromTermType(Long type) {
    long env = getEnv();
    if (msat_is_bool_type(env, type)) {
      return FormulaType.BooleanType;
    } else if (msat_is_integer_type(env, type)) {
      return FormulaType.IntegerType;
    } else if (msat_is_rational_type(env, type)) {
      return FormulaType.RationalType;
    } else if (msat_is_bv_type(env, type)) {
      return FormulaType.getBitvectorTypeWithSize(msat_get_bv_type_size(env, type));
    } else if (msat_is_fp_type(env, type)) {
      return FormulaType.getFloatingPointType(
          msat_get_fp_type_exp_width(env, type), msat_get_fp_type_mant_width(env, type));
    } else if (msat_is_fp_roundingmode_type(env, type)) {
      return FormulaType.FloatingPointRoundingModeType;
    } else if (msat_is_array_type(env, type)) {
      long indexType = msat_get_array_index_type(env, type);
      long elementType = msat_get_array_element_type(env, type);
      return FormulaType.getArrayType(
          getFormulaTypeFromTermType(indexType), getFormulaTypeFromTermType(elementType));
    }
    throw new IllegalArgumentException("Unknown formula type " + msat_type_repr(type));
  }

  @Override
  public Long getBitvectorType(int pBitwidth) {
    return msat_get_bv_type(getEnv(), pBitwidth);
  }

  @Override
  public Long getFloatingPointType(FloatingPointType pType) {
    return msat_get_fp_type(getEnv(), pType.getExponentSize(), pType.getMantissaSize());
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, Long pTerm) {
    assert pType.equals(getFormulaType(pTerm))
            || (pType.equals(FormulaType.RationalType)
                && getFormulaType(pTerm).equals(FormulaType.IntegerType))
        : String.format(
            "Trying to encapsulate formula of type %s as %s", getFormulaType(pTerm), pType);
    if (pType.isBooleanType()) {
      return (T) new Mathsat5BooleanFormula(pTerm);
    } else if (pType.isIntegerType()) {
      return (T) new Mathsat5IntegerFormula(pTerm);
    } else if (pType.isRationalType()) {
      return (T) new Mathsat5RationalFormula(pTerm);
    } else if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrFt = (ArrayFormulaType<?, ?>) pType;
      return (T) new Mathsat5ArrayFormula<>(pTerm, arrFt.getIndexType(), arrFt.getElementType());
    } else if (pType.isBitvectorType()) {
      return (T) new Mathsat5BitvectorFormula(pTerm);
    } else if (pType.isFloatingPointType()) {
      return (T) new Mathsat5FloatingPointFormula(pTerm);
    } else if (pType.isFloatingPointRoundingModeType()) {
      return (T) new Mathsat5FloatingPointRoundingModeFormula(pTerm);
    }
    throw new IllegalArgumentException("Cannot create formulas of type " + pType + " in MathSAT");
  }

  @Override
  public BooleanFormula encapsulateBoolean(Long pTerm) {
    assert getFormulaType(pTerm).isBooleanType();
    return new Mathsat5BooleanFormula(pTerm);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Long pTerm) {
    assert getFormulaType(pTerm).isBitvectorType();
    return new Mathsat5BitvectorFormula(pTerm);
  }

  @Override
  protected FloatingPointFormula encapsulateFloatingPoint(Long pTerm) {
    assert getFormulaType(pTerm).isFloatingPointType();
    return new Mathsat5FloatingPointFormula(pTerm);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      Long pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType));
    return new Mathsat5ArrayFormula<>(pTerm, pIndexType, pElementType);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> FormulaType<TE> getArrayFormulaElementType(
      ArrayFormula<TI, TE> pArray) {
    return ((Mathsat5ArrayFormula<TI, TE>) pArray).getElementType();
  }

  @Override
  protected <TI extends Formula, TE extends Formula> FormulaType<TI> getArrayFormulaIndexType(
      ArrayFormula<TI, TE> pArray) {
    return ((Mathsat5ArrayFormula<TI, TE>) pArray).getIndexType();
  }

  @Override
  public Long getArrayType(Long pIndexType, Long pElementType) {
    return msat_get_array_type(getEnv(), pIndexType, pElementType);
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, final Long f) {
    int arity = msat_term_arity(f);
    if (msat_term_is_number(environment, f)) {
      return visitor.visitConstant(formula, convertValue(f, f));
    } else if (msat_term_is_true(environment, f)) {
      return visitor.visitConstant(formula, true);
    } else if (msat_term_is_false(environment, f)) {
      return visitor.visitConstant(formula, false);
    } else if (msat_term_is_constant(environment, f)) {
      return visitor.visitFreeVariable(formula, msat_term_repr(f));
    } else {

      ImmutableList.Builder<Formula> args = ImmutableList.builder();
      ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();
      for (int i = 0; i < arity; i++) {
        long arg = msat_term_get_arg(f, i);
        FormulaType<?> argumentType = getFormulaType(arg);
        args.add(encapsulate(argumentType, arg));
        argTypes.add(argumentType);
      }

      String name = msat_decl_get_name(msat_term_get_decl(f));
      return visitor.visitFunction(
          formula,
          args.build(),
          FunctionDeclarationImpl.of(
              name,
              getDeclarationKind(f),
              argTypes.build(),
              getFormulaType(f),
              msat_term_get_decl(f)));
    }
  }

  String getName(long term) {
    if (msat_term_is_uf(environment, term)) {
      return msat_decl_get_name(msat_term_get_decl(term));
    }
    return msat_term_repr(term);
  }

  private FunctionDeclarationKind getDeclarationKind(long pF) {
    if (msat_term_is_uf(environment, pF)) {
      return FunctionDeclarationKind.UF;
    }

    assert !msat_term_is_constant(environment, pF) : "Variables should be handled somewhere else";

    long decl = msat_term_get_decl(pF);
    int tag = msat_decl_get_tag(environment, decl);
    switch (tag) {
      case MSAT_TAG_AND:
        return FunctionDeclarationKind.AND;
      case MSAT_TAG_NOT:
        return FunctionDeclarationKind.NOT;
      case MSAT_TAG_OR:
        return FunctionDeclarationKind.OR;
      case MSAT_TAG_IFF:
        return FunctionDeclarationKind.IFF;
      case MSAT_TAG_ITE:
        return FunctionDeclarationKind.ITE;

      case MSAT_TAG_PLUS:
        return FunctionDeclarationKind.ADD;
      case MSAT_TAG_LEQ:
        return FunctionDeclarationKind.LTE;
      case MSAT_TAG_EQ:
        return FunctionDeclarationKind.EQ;
      case MSAT_TAG_ARRAY_READ:
        return FunctionDeclarationKind.SELECT;
      case MSAT_TAG_ARRAY_WRITE:
        return FunctionDeclarationKind.STORE;

      case MSAT_TAG_BV_EXTRACT:
        return FunctionDeclarationKind.BV_EXTRACT;
      case MSAT_TAG_BV_CONCAT:
        return FunctionDeclarationKind.BV_CONCAT;
      case MSAT_TAG_BV_NOT:
        return FunctionDeclarationKind.BV_NOT;
      case MSAT_TAG_BV_NEG:
        return FunctionDeclarationKind.BV_NEG;
      case MSAT_TAG_BV_AND:
        return FunctionDeclarationKind.BV_AND;
      case MSAT_TAG_BV_OR:
        return FunctionDeclarationKind.BV_OR;
      case MSAT_TAG_BV_XOR:
        return FunctionDeclarationKind.BV_XOR;
      case MSAT_TAG_BV_ULT:
        return FunctionDeclarationKind.BV_ULT;
      case MSAT_TAG_BV_SLT:
        return FunctionDeclarationKind.BV_SLT;
      case MSAT_TAG_BV_ULE:
        return FunctionDeclarationKind.BV_ULE;
      case MSAT_TAG_BV_SLE:
        return FunctionDeclarationKind.BV_SLE;
      case MSAT_TAG_BV_ADD:
        return FunctionDeclarationKind.BV_ADD;
      case MSAT_TAG_BV_SUB:
        return FunctionDeclarationKind.BV_SUB;
      case MSAT_TAG_BV_MUL:
        return FunctionDeclarationKind.BV_MUL;
      case MSAT_TAG_BV_UDIV:
        return FunctionDeclarationKind.BV_UDIV;
      case MSAT_TAG_BV_SDIV:
        return FunctionDeclarationKind.BV_SDIV;
      case MSAT_TAG_BV_UREM:
        return FunctionDeclarationKind.BV_UREM;
      case MSAT_TAG_BV_SREM:
        return FunctionDeclarationKind.BV_SREM;
      case MSAT_TAG_BV_LSHL:
        return FunctionDeclarationKind.BV_SHL;
      case MSAT_TAG_BV_LSHR:
        return FunctionDeclarationKind.BV_LSHR;
      case MSAT_TAG_BV_ASHR:
        return FunctionDeclarationKind.BV_ASHR;

      case MSAT_TAG_FP_NEG:
        return FunctionDeclarationKind.FP_NEG;
      case MSAT_TAG_FP_ADD:
        return FunctionDeclarationKind.FP_ADD;
      case MSAT_TAG_FP_SUB:
        return FunctionDeclarationKind.FP_SUB;
      case MSAT_TAG_FP_DIV:
        return FunctionDeclarationKind.FP_DIV;
      case MSAT_TAG_FP_MUL:
        return FunctionDeclarationKind.FP_MUL;
      case MSAT_TAG_FP_LT:
        return FunctionDeclarationKind.FP_LT;
      case MSAT_TAG_FP_LE:
        return FunctionDeclarationKind.FP_LE;
      case MSAT_TAG_FP_EQ:
        return FunctionDeclarationKind.FP_EQ;
      case MSAT_TAG_FP_ROUND_TO_INT:
        return FunctionDeclarationKind.FP_ROUND_TO_INTEGRAL;

      case MSAT_TAG_UNKNOWN:
        switch (msat_decl_get_name(decl)) {
          case "`fprounding_even`":
            return FunctionDeclarationKind.FP_ROUND_EVEN;
          case "`fprounding_plus_inf`":
            return FunctionDeclarationKind.FP_ROUND_POSITIVE;
          case "`fprounding_minus_inf`":
            return FunctionDeclarationKind.FP_ROUND_NEGATIVE;
          case "`fprounding_zero`":
            return FunctionDeclarationKind.FP_ROUND_ZERO;

          default:
            return FunctionDeclarationKind.OTHER;
        }

      default:
        return FunctionDeclarationKind.OTHER;
    }
  }

  Object convertValue(long key, long term) {

    // To get the correct type, we generate it from the key, not the value.
    FormulaType<?> type = getFormulaType(key);
    String repr = msat_term_repr(term);
    if (type.isBooleanType()) {
      return msat_term_is_true(getEnv(), term);
    } else if (type.isRationalType()) {
      return Rational.ofString(repr);
    } else if (type.isIntegerType()) {
      return new BigInteger(repr);
    } else if (type.isBitvectorType()) {
      return parseBitvector(repr);
    } else if (type.isFloatingPointType()) {
      return parseFloatingPoint(repr);
    } else {

      throw new IllegalArgumentException("Unexpected type: " + type);
    }
  }

  private Number parseFloatingPoint(String lTermRepresentation) {

    // the term is of the format "<VALUE>_<EXPWIDTH>_<MANTWIDTH>"
    Matcher matcher = FLOATING_POINT_PATTERN.matcher(lTermRepresentation);
    if (!matcher.matches()) {
      throw new NumberFormatException("Unknown floating-point format: " + lTermRepresentation);
    }

    int expWidth = Integer.parseInt(matcher.group(2));
    int mantWidth = Integer.parseInt(matcher.group(3));

    if (expWidth == 11 && mantWidth == 52) {
      return Double.longBitsToDouble(UnsignedLong.valueOf(matcher.group(1)).longValue());
    } else if (expWidth == 8 && mantWidth == 23) {
      return Float.intBitsToFloat(UnsignedInteger.valueOf(matcher.group(1)).intValue());
    }

    // TODO to be fully correct, we would need to interpret this string
    return new BigInteger(matcher.group(1));
  }

  // TODO: change this to the latest version
  // (if possible try to use a BitvectorFormula instance here)
  private static BigInteger parseBitvector(String lTermRepresentation) {
    // the term is of the format "<VALUE>_<WIDTH>"
    Matcher matcher = BITVECTOR_PATTERN.matcher(lTermRepresentation);
    if (!matcher.matches()) {
      throw new NumberFormatException("Unknown bitvector format: " + lTermRepresentation);
    }

    // TODO: calculate negative value?
    String term = matcher.group(1);
    return new BigInteger(term);
  }

  @Override
  public Long callFunctionImpl(FunctionDeclarationImpl<?, Long> declaration, List<Long> args) {
    return msat_make_term(environment, declaration.getSolverDeclaration(), Longs.toArray(args));
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(Long pLong) {
    return msat_term_get_decl(pLong);
  }
}
