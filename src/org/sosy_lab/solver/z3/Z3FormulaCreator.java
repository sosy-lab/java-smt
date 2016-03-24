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
package org.sosy_lab.solver.z3;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.solver.z3.Z3NativeApi.ast_to_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.fpa_get_ebits;
import static org.sosy_lab.solver.z3.Z3NativeApi.fpa_get_sbits;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_arg;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_decl;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_num_args;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_arity;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_array_sort_domain;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_array_sort_range;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_ast_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_bv_sort_size;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_decl_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_decl_name;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_index_value;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_numeral_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_quantifier_body;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_quantifier_bound_name;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_quantifier_bound_sort;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_quantifier_num_bound;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_sort;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_sort_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_symbol_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_symbol_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.is_algebraic_number;
import static org.sosy_lab.solver.z3.Z3NativeApi.is_numeral_ast;
import static org.sosy_lab.solver.z3.Z3NativeApi.is_quantifier_forall;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_app;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_bv_sort;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_const;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_fpa_to_real;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_string_symbol;
import static org.sosy_lab.solver.z3.Z3NativeApi.model_dec_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.simplify;
import static org.sosy_lab.solver.z3.Z3NativeApi.sort_to_ast;
import static org.sosy_lab.solver.z3.Z3NativeApi.sort_to_string;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_APP_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_ARRAY_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_BOOL_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_BV_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_FLOATING_POINT_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_FUNC_DECL_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_INT_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_NUMERAL_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_ADD;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_AND;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_DISTINCT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_DIV;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_EQ;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_FALSE;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_FPA_MINUS_INF;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_FPA_MINUS_ZERO;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_FPA_NAN;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_FPA_NUM;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_FPA_PLUS_INF;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_FPA_PLUS_ZERO;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_GE;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_GT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_IFF;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_IMPLIES;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_ITE;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_LE;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_LT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_MOD;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_MUL;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_NOT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_OR;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_SELECT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_STORE;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_SUB;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_TRUE;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_UNINTERPRETED;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_XOR;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_QUANTIFIER_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_REAL_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_ROUNDING_MODE_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_SORT_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_STRING_SYMBOL;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_UNKNOWN_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_VAR_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.isOP;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Maps;
import com.google.common.collect.Table;
import com.google.common.primitives.Longs;

import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.common.time.Timer;
import org.sosy_lab.solver.api.ArrayFormula;
import org.sosy_lab.solver.api.BitvectorFormula;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.FloatingPointFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.solver.api.FunctionDeclarationKind;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.solver.basicimpl.FormulaCreator;
import org.sosy_lab.solver.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.solver.visitors.FormulaVisitor;
import org.sosy_lab.solver.z3.Z3Formula.Z3ArrayFormula;
import org.sosy_lab.solver.z3.Z3Formula.Z3BitvectorFormula;
import org.sosy_lab.solver.z3.Z3Formula.Z3BooleanFormula;
import org.sosy_lab.solver.z3.Z3Formula.Z3FloatingPointFormula;
import org.sosy_lab.solver.z3.Z3Formula.Z3FloatingPointRoundingModeFormula;
import org.sosy_lab.solver.z3.Z3Formula.Z3IntegerFormula;
import org.sosy_lab.solver.z3.Z3Formula.Z3RationalFormula;

import java.lang.ref.PhantomReference;
import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

@Options(prefix = "solver.z3")
class Z3FormulaCreator extends FormulaCreator<Long, Long, Long, Long> {

  private static final Map<Integer, Object> Z3_CONSTANTS =
      ImmutableMap.<Integer, Object>builder()
          .put(Z3_OP_TRUE, true)
          .put(Z3_OP_FALSE, false)
          .put(Z3_OP_FPA_PLUS_ZERO, +0.0)
          .put(Z3_OP_FPA_MINUS_ZERO, -0.0)
          .put(Z3_OP_FPA_PLUS_INF, Double.POSITIVE_INFINITY)
          .put(Z3_OP_FPA_MINUS_INF, Double.NEGATIVE_INFINITY)
          .put(Z3_OP_FPA_NAN, Double.NaN)
          .build();


  @Option(secure = true, description = "Whether to use PhantomReferences for discarding Z3 AST")
  private boolean usePhantomReferences = false;

  private final Table<Long, Long, Long> allocatedArraySorts = HashBasedTable.create();

  /**
   * Automatic clean-up of Z3 ASTs.
   */
  private final ReferenceQueue<Z3Formula> referenceQueue = new ReferenceQueue<>();
  private final Map<PhantomReference<? extends Z3Formula>, Long> referenceMap =
      Maps.newIdentityHashMap();

  /**
   * Automatic clean-up of Z3Models.
   */
  private final ReferenceQueue<Z3Model> modelReferenceQueue = new ReferenceQueue<>();
  private final Map<PhantomReference<? extends Z3Model>, Long> modelReferenceMap =
      Maps.newIdentityHashMap();

  // todo: getters for statistic.
  private final Timer cleanupTimer = new Timer();

  Z3FormulaCreator(
      long pEnv, long pBoolType, long pIntegerType, long pRealType, Configuration config)
      throws InvalidConfigurationException {
    super(pEnv, pBoolType, pIntegerType, pRealType);
    config.inject(this);
  }

  @Override
  public Long makeVariable(Long type, String varName) {
    long z3context = getEnv();
    long symbol = mk_string_symbol(z3context, varName);
    return mk_const(z3context, symbol, type);
  }

  @Override
  public Long extractInfo(Formula pT) {
    return Z3FormulaManager.getZ3Expr(pT);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    Long term = extractInfo(pFormula);
    return (FormulaType<T>) getFormulaType(term);
  }

  public FormulaType<?> getFormulaTypeFromSort(Long pSort) {
    long z3context = getEnv();
    long sortKind = get_sort_kind(z3context, pSort);
    if (sortKind == Z3_BOOL_SORT) {
      return FormulaType.BooleanType;
    } else if (sortKind == Z3_INT_SORT) {
      return FormulaType.IntegerType;
    } else if (sortKind == Z3_ARRAY_SORT) {
      long domainSort = get_array_sort_domain(z3context, pSort);
      long rangeSort = get_array_sort_range(z3context, pSort);
      return FormulaType.getArrayType(
          getFormulaTypeFromSort(domainSort), getFormulaTypeFromSort(rangeSort));
    } else if (sortKind == Z3_REAL_SORT) {
      return FormulaType.RationalType;
    } else if (sortKind == Z3_BV_SORT) {
      return FormulaType.getBitvectorTypeWithSize(get_bv_sort_size(z3context, pSort));
    } else if (sortKind == Z3_FLOATING_POINT_SORT) {
      return FormulaType.getFloatingPointType(
          fpa_get_ebits(z3context, pSort), fpa_get_sbits(z3context, pSort));
    } else if (sortKind == Z3_ROUNDING_MODE_SORT) {
      return FormulaType.FloatingPointRoundingModeType;
    }
    throw new IllegalArgumentException(
        "Unknown formula type " + sort_to_string(z3context, pSort) + " with kind " + sortKind);
  }

  @Override
  public FormulaType<?> getFormulaType(Long pFormula) {
    long sort = get_sort(getEnv(), pFormula);
    return getFormulaTypeFromSort(sort);
  }

  @Override
  protected <TD extends Formula, TR extends Formula> FormulaType<TR> getArrayFormulaElementType(
      ArrayFormula<TD, TR> pArray) {
    return ((Z3ArrayFormula<TD, TR>) pArray).getElementType();
  }

  @Override
  protected <TD extends Formula, TR extends Formula> FormulaType<TD> getArrayFormulaIndexType(
      ArrayFormula<TD, TR> pArray) {
    return ((Z3ArrayFormula<TD, TR>) pArray).getIndexType();
  }

  @Override
  protected <TD extends Formula, TR extends Formula> ArrayFormula<TD, TR> encapsulateArray(
      Long pTerm, FormulaType<TD> pIndexType, FormulaType<TR> pElementType) {
    assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType));
    cleanupReferences();
    return storePhantomReference(
        new Z3ArrayFormula<>(getEnv(), pTerm, pIndexType, pElementType), pTerm);
  }

  private <T extends Z3Formula> T storePhantomReference(T out, Long pTerm) {
    if (usePhantomReferences) {
      PhantomReference<T> ref = new PhantomReference<>(out, referenceQueue);
      referenceMap.put(ref, pTerm);
    }
    return out;
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, Long pTerm) {
    assert pType.equals(getFormulaType(pTerm))
            || (pType.equals(FormulaType.RationalType)
                && getFormulaType(pTerm).equals(FormulaType.IntegerType))
        : String.format(
            "Trying to encapsulate formula of type %s as %s", getFormulaType(pTerm), pType);
    cleanupReferences();
    if (pType.isBooleanType()) {
      return (T) storePhantomReference(new Z3BooleanFormula(getEnv(), pTerm), pTerm);
    } else if (pType.isIntegerType()) {
      return (T) storePhantomReference(new Z3IntegerFormula(getEnv(), pTerm), pTerm);
    } else if (pType.isRationalType()) {
      return (T) storePhantomReference(new Z3RationalFormula(getEnv(), pTerm), pTerm);
    } else if (pType.isBitvectorType()) {
      return (T) storePhantomReference(new Z3BitvectorFormula(getEnv(), pTerm), pTerm);
    } else if (pType.isFloatingPointType()) {
      return (T) storePhantomReference(new Z3FloatingPointFormula(getEnv(), pTerm), pTerm);
    } else if (pType.isFloatingPointRoundingModeType()) {
      return (T)
          storePhantomReference(new Z3FloatingPointRoundingModeFormula(getEnv(), pTerm), pTerm);
    } else if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrFt = (ArrayFormulaType<?, ?>) pType;
      return (T)
          storePhantomReference(
              new Z3ArrayFormula<>(getEnv(), pTerm, arrFt.getIndexType(), arrFt.getElementType()),
              pTerm);
    }

    throw new IllegalArgumentException("Cannot create formulas of type " + pType + " in Z3");
  }

  @Override
  public BooleanFormula encapsulateBoolean(Long pTerm) {
    assert getFormulaType(pTerm).isBooleanType();
    cleanupReferences();
    return storePhantomReference(new Z3BooleanFormula(getEnv(), pTerm), pTerm);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Long pTerm) {
    assert getFormulaType(pTerm).isBitvectorType();
    cleanupReferences();
    return storePhantomReference(new Z3BitvectorFormula(getEnv(), pTerm), pTerm);
  }

  @Override
  protected FloatingPointFormula encapsulateFloatingPoint(Long pTerm) {
    assert getFormulaType(pTerm).isFloatingPointType();
    cleanupReferences();
    return storePhantomReference(new Z3FloatingPointFormula(getEnv(), pTerm), pTerm);
  }

  @Override
  public Long getArrayType(Long pIndexType, Long pElementType) {
    Long allocatedArraySort = allocatedArraySorts.get(pIndexType, pElementType);
    if (allocatedArraySort == null) {
      allocatedArraySort = Z3NativeApi.mk_array_sort(getEnv(), pIndexType, pElementType);
      Z3NativeApi.inc_ref(getEnv(), allocatedArraySort);
      allocatedArraySorts.put(pIndexType, pElementType, allocatedArraySort);
    }
    return allocatedArraySort;
  }

  @Override
  public Long getBitvectorType(int pBitwidth) {
    checkArgument(pBitwidth > 0, "Cannot use bitvector type with size %s", pBitwidth);
    long bvSort = mk_bv_sort(getEnv(), pBitwidth);
    inc_ref(getEnv(), sort_to_ast(getEnv(), bvSort));
    return bvSort;
  }

  @Override
  public Long getFloatingPointType(FormulaType.FloatingPointType type) {
    long fpSort = Z3NativeApi.mk_fpa_sort(getEnv(), type.getExponentSize(), type.getMantissaSize());
    inc_ref(getEnv(), sort_to_ast(getEnv(), fpSort));
    return fpSort;
  }

  private void cleanupReferences() {
    if (!usePhantomReferences) {
      return;
    }
    cleanupTimer.start();
    try {
      Reference<? extends Z3Formula> ref;
      while ((ref = referenceQueue.poll()) != null) {
        long z3ast = referenceMap.remove(ref);
        dec_ref(environment, z3ast);
      }
    } finally {
      cleanupTimer.stop();
    }
  }

  void storeModelPhantomReference(Z3Model model, long nativeModel) {

    // NB: this is not protected by the usePhantomReferences option, as there
    // are relatively few model objects.
    PhantomReference<Z3Model> ref = new PhantomReference<>(model, modelReferenceQueue);
    modelReferenceMap.put(ref, nativeModel);
  }

  void cleanupModelReferences() {
    Reference<? extends Z3Model> ref;
    cleanupTimer.start();
    while ((ref = modelReferenceQueue.poll()) != null) {
      long z3model = modelReferenceMap.remove(ref);
      model_dec_ref(environment, z3model);
    }
    cleanupTimer.stop();
  }

  private Long replaceArgs(Long t, List<Long> newArgs) {
    Preconditions.checkState(get_app_num_args(environment, t) == newArgs.size());
    long[] newParams = Longs.toArray(newArgs);
    // TODO check equality of sort of each oldArg and newArg
    long funcDecl = get_app_decl(environment, t);
    return mk_app(environment, funcDecl, newParams);
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, final Formula formula, final Long f) {
    switch (get_ast_kind(environment, f)) {
      case Z3_NUMERAL_AST:
        return visitor.visitConstant(formula, convertValue(f));
      case Z3_APP_AST:
        long funcDecl = get_app_decl(environment, f);
        long symbol = get_decl_name(environment, funcDecl);
        assert get_symbol_kind(environment, symbol) == Z3_STRING_SYMBOL;
        String name = get_symbol_string(environment, symbol);
        int arity = get_app_num_args(environment, f);

        if (arity == 0) {

          // constants
          int declKind = get_decl_kind(environment, get_app_decl(environment, f));
          Object value = Z3_CONSTANTS.get(declKind);
          if (value != null) {
            return visitor.visitConstant(formula, value);

          } else if (declKind == Z3_OP_FPA_NUM
              || get_sort_kind(environment, get_sort(environment, f)) == Z3_ROUNDING_MODE_SORT) {
            return visitor.visitConstant(formula, convertValue(f));

          } else {

            // Has to be a variable otherwise.
            // TODO: assert that.
            return visitor.visitFreeVariable(formula, name);
          }
        }

        ImmutableList.Builder<Formula> args = ImmutableList.builder();
        ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();
        for (int i = 0; i < arity; i++) {
          long arg = get_app_arg(environment, f, i);
          FormulaType<?> argumentType = getFormulaType(arg);
          args.add(encapsulate(argumentType, arg));
          argTypes.add(argumentType);
        }
        return visitor.visitFunction(
            formula,
            args.build(),
            FunctionDeclarationImpl.of(
                name,
                getDeclarationKind(f),
                argTypes.build(),
                getFormulaType(f),
                funcDecl
            )
        );
      case Z3_VAR_AST:
        int deBruijnIdx = get_index_value(environment, f);
        return visitor.visitBoundVariable(formula, deBruijnIdx);
      case Z3_QUANTIFIER_AST:
        BooleanFormula body = encapsulateBoolean(get_quantifier_body(environment, f));
        Quantifier q = is_quantifier_forall(environment, f) ? Quantifier.FORALL : Quantifier.EXISTS;
        return visitor.visitQuantifier((BooleanFormula) formula, q, getBoundVars(f), body);

      case Z3_SORT_AST:
      case Z3_FUNC_DECL_AST:
      case Z3_UNKNOWN_AST:
      default:
        throw new UnsupportedOperationException(
            "Input should be a formula AST, " + "got unexpected type instead");
    }
  }

  private List<Formula> getBoundVars(long f) {
    int numBound = get_quantifier_num_bound(environment, f);
    List<Formula> boundVars = new ArrayList<>(numBound);
    for (int i = 0; i < numBound; i++) {
      long varName = get_quantifier_bound_name(environment, f, i);
      long varSort = get_quantifier_bound_sort(environment, f, i);
      boundVars.add(
          encapsulate(getFormulaTypeFromSort(varSort), mk_const(environment, varName, varSort)));
    }
    return boundVars;
  }

  private FunctionDeclarationKind getDeclarationKind(long f) {
    int decl = get_decl_kind(environment, get_app_decl(environment, f));

    assert get_arity(environment, get_app_decl(environment, f)) > 0
        : "Variables should be handled somewhere else.";
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

      case Z3_OP_STORE:
        return FunctionDeclarationKind.STORE;
      case Z3_OP_SELECT:
        return FunctionDeclarationKind.SELECT;

      default:
        return FunctionDeclarationKind.OTHER;
    }
  }

  /**
   * @param value Z3_ast
   * @return Whether the value is a constant and can be passed to {@link #convertValue(long)}.
   */
  public boolean isConstant(long value) {
    return is_numeral_ast(environment, value)
        || is_algebraic_number(environment, value)
        || isOP(environment, value, Z3_OP_TRUE)
        || isOP(environment, value, Z3_OP_FALSE);
  }

  /**
   * @param value Z3_ast representing a *value*.
   * @return BigInteger|Double|Rational.
   */
  public Object convertValue(long value) {
    assert isConstant(value);
    inc_ref(environment, value);

    Object constantValue =
        Z3_CONSTANTS.get(get_decl_kind(environment, get_app_decl(environment, value)));
    if (constantValue != null) {
      return constantValue;
    }

    try {
      FormulaType<?> type = getFormulaType(value);
      if (type.isBooleanType()) {
        return isOP(environment, value, Z3_OP_TRUE);
      } else if (type.isIntegerType()) {
        return new BigInteger(get_numeral_string(environment, value));
      } else if (type.isRationalType()) {
        return Rational.ofString(get_numeral_string(environment, value));
      } else if (type.isBitvectorType()) {
        return new BigInteger(get_numeral_string(environment, value));
      } else if (type.isFloatingPointType()) {
        // Converting to Rational and reading that is easier.
        return convertValue(simplify(environment, mk_fpa_to_real(environment, value)));

      } else {

        // Unknown type --- return string serialization.
        return ast_to_string(environment, value);
      }

    } finally {
      dec_ref(environment, value);
    }
  }

  @Override
  public Long callFunctionImpl(
      FunctionDeclarationImpl<?, Long> declaration, List<Long> args) {
    return Z3NativeApi.mk_app(
        environment,
        declaration.getSolverDeclaration(),
        Longs.toArray(args)
    );
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(Long pLong) {
    return get_app_decl(getEnv(), pLong);
  }
}
