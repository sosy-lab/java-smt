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
package org.sosy_lab.solver.mathsat5;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_AND;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_ARRAY_READ;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_ARRAY_WRITE;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_EQ;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_IFF;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_ITE;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_LEQ;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_NOT;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_OR;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_PLUS;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_decl_get_name;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_decl_get_tag;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_declare_function;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_destroy_model;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_array_element_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_array_index_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_array_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_bool_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_bv_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_bv_type_size;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_fp_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_fp_type_exp_width;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_fp_type_mant_width;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_integer_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_get_rational_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_is_array_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_is_bool_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_is_bv_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_is_fp_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_is_integer_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_is_rational_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_constant;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_term;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_arity;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_get_arg;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_get_decl;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_get_type;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_constant;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_false;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_number;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_true;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_uf;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_repr;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_type_repr;

import com.google.common.base.Function;
import com.google.common.collect.Maps;
import com.google.common.primitives.Longs;

import org.sosy_lab.solver.api.ArrayFormula;
import org.sosy_lab.solver.api.BitvectorFormula;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.FloatingPointFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.solver.api.FormulaType.FloatingPointType;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.FunctionDeclarationKind;
import org.sosy_lab.solver.basicimpl.FormulaCreator;
import org.sosy_lab.solver.mathsat5.Mathsat5Formula.Mathsat5ArrayFormula;
import org.sosy_lab.solver.mathsat5.Mathsat5Formula.Mathsat5BitvectorFormula;
import org.sosy_lab.solver.mathsat5.Mathsat5Formula.Mathsat5BooleanFormula;
import org.sosy_lab.solver.mathsat5.Mathsat5Formula.Mathsat5FloatingPointFormula;
import org.sosy_lab.solver.mathsat5.Mathsat5Formula.Mathsat5IntegerFormula;
import org.sosy_lab.solver.mathsat5.Mathsat5Formula.Mathsat5RationalFormula;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import java.lang.ref.PhantomReference;
import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

class Mathsat5FormulaCreator extends FormulaCreator<Long, Long, Long> {

  /**
   * Automatic clean-up of Mathsat5 models.
   */
  private final ReferenceQueue<Mathsat5Model> modelReferenceQueue = new ReferenceQueue<>();
  private final Map<PhantomReference<? extends Mathsat5Model>, Long> modelReferenceMap =
      Maps.newIdentityHashMap();

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
    } else if (msat_is_array_type(env, type)) {
      long indexType = msat_get_array_index_type(env, type);
      long elementType = msat_get_array_element_type(env, type);
      return FormulaType.getArrayType(
          getFormulaTypeFromTermType(indexType), getFormulaTypeFromTermType(elementType));
    }
    throw new IllegalArgumentException(
        "Unknown formula type " + msat_type_repr(type) + " for term " + msat_term_repr(type));
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
    //    Long allocatedArraySort = allocatedArraySorts.get(pIndexType, pElementType);
    //    if (allocatedArraySort == null) {
    //      allocatedArraySort = msat_make_array_const(getEnv(), pIndexType, pElementType);
    //      allocatedArraySorts.put(pIndexType, pElementType, allocatedArraySort);
    //    }
    //    return allocatedArraySort;
    return msat_get_array_type(getEnv(), pIndexType, pElementType);
    //throw new IllegalArgumentException("MathSAT5.getArrayType(): Implement me!");
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, final Long f) {
    int arity = msat_term_arity(f);
    if (msat_term_is_number(environment, f)) {

      // TODO extract logic from Mathsat5Model for conversion from string to number and use it here
      return visitor.visitConstant(formula, msat_term_repr(f));
    } else if (msat_term_is_true(environment, f)) {
      return visitor.visitConstant(formula, true);
    } else if (msat_term_is_false(environment, f)) {
      return visitor.visitConstant(formula, false);
    } else if (msat_term_is_constant(environment, f)) {
      return visitor.visitFreeVariable(formula, msat_term_repr(f));
    } else {

      List<Formula> args = new ArrayList<>(arity);
      for (int i = 0; i < arity; i++) {
        long arg = msat_term_get_arg(f, i);
        FormulaType<?> argumentType = getFormulaType(arg);
        args.add(encapsulate(argumentType, arg));
      }

      String name = msat_decl_get_name(msat_term_get_decl(f));

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
    }
  }

  String getName(long term) {
    if (msat_term_is_uf(environment, term)) {
      return msat_decl_get_name(msat_term_get_decl(term));
    }
    return msat_term_repr(term);
  }

  private Long replaceArgs(Long t, List<Long> newArgs) {
    long tDecl = msat_term_get_decl(t);
    return msat_make_term(environment, tDecl, Longs.toArray(newArgs));
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
      default:
        return FunctionDeclarationKind.OTHER;
    }
  }

  public void storeModelPhantomReference(Mathsat5Model out, long model) {
    PhantomReference<Mathsat5Model> ref = new PhantomReference<>(out, modelReferenceQueue);
    modelReferenceMap.put(ref, model);
  }

  public void cleanupModelReferences() {
    Reference<? extends Mathsat5Model> ref;
    while ((ref = modelReferenceQueue.poll()) != null) {
      long model = modelReferenceMap.remove(ref);
      msat_destroy_model(model);
    }

  }
}
