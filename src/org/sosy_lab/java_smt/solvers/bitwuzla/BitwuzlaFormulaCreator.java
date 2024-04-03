// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_AND;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_APPLY;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_ARRAY_SELECT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_ARRAY_STORE;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_ADD;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_AND;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_ASHR;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_CONCAT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_EXTRACT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_MUL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_NEG;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_NOT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_OR;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_SDIV;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_SGE;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_SGT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_SHL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_SIGN_EXTEND;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_SLE;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_SLT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_SMOD;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_SREM;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_SUB;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_UDIV;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_UGE;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_UGT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_ULE;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_ULT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_UREM;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_XOR;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_BV_ZERO_EXTEND;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_CONSTANT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_DISTINCT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_EQUAL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_EXISTS;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FORALL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_ABS;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_ADD;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_DIV;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_EQUAL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_GEQ;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_GT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_IS_INF;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_IS_NAN;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_IS_NEG;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_IS_NORMAL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_IS_SUBNORMAL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_IS_ZERO;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_LEQ;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_LT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_MAX;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_MIN;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_MUL;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_NEG;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_RTI;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_SQRT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_SUB;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_TO_FP_FROM_BV;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_TO_FP_FROM_FP;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_TO_FP_FROM_SBV;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_TO_FP_FROM_UBV;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_TO_SBV;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_FP_TO_UBV;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_IFF;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_IMPLIES;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_ITE;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_NOT;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_OR;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_VALUE;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.BITWUZLA_KIND_XOR;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Table;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.stream.LongStream;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaFormula.BitwuzlaArrayFormula;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaFormula.BitwuzlaBitvectorFormula;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaFormula.BitwuzlaBooleanFormula;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaFormula.BitwuzlaFloatingPointFormula;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaFormula.BitwuzlaFloatingPointRoundingModeFormula;

public class BitwuzlaFormulaCreator extends FormulaCreator<Long, Long, Long, BitwuzlaDeclaration> {
  private final Table<String, Long, Long> formulaCache = HashBasedTable.create();

  // private final Table<String, Long, Long> boundFormulaCache = HashBasedTable.create();

  protected BitwuzlaFormulaCreator(Long pBitwuzlaEnv) {
    super(pBitwuzlaEnv, BitwuzlaJNI.bitwuzla_mk_bool_sort(), null, null, null, null);
  }

  @Override
  public Long getBitvectorType(int bitwidth) {
    return BitwuzlaJNI.bitwuzla_mk_bv_sort(bitwidth);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Long pTerm) {
    assert getFormulaType(pTerm).isBitvectorType()
        : "Unexpected formula type for BV formula: " + getFormulaType(pTerm);
    return new BitwuzlaBitvectorFormula(pTerm);
  }

  // Assuming that JavaSMT FloatingPointType follows IEEE 754, if it is in the decimal
  // system instead use bitwuzla_mk_fp_value_from_real somehow or convert myself
  @Override
  public Long getFloatingPointType(FloatingPointType type) {
    long fpSort =
        BitwuzlaJNI.bitwuzla_mk_fp_sort(type.getExponentSize(), type.getMantissaSize() + 1);
    return fpSort;
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> FormulaType<TE> getArrayFormulaElementType(
      ArrayFormula<TI, TE> pArray) {
    return ((BitwuzlaArrayFormula<TI, TE>) pArray).getElementType();
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> FormulaType<TI> getArrayFormulaIndexType(
      ArrayFormula<TI, TE> pArray) {
    return ((BitwuzlaArrayFormula<TI, TE>) pArray).getIndexType();
  }

  @Override
  public Long getArrayType(Long indexType, Long elementType) {
    return BitwuzlaJNI.bitwuzla_mk_array_sort(indexType, elementType);
  }

  @Override
  protected FloatingPointFormula encapsulateFloatingPoint(Long pTerm) {
    assert getFormulaType(pTerm).isFloatingPointType()
        : String.format(
            "%s is no FP, but %s (%s)",
            pTerm, BitwuzlaJNI.bitwuzla_term_get_sort(pTerm), getFormulaType(pTerm));
    return new BitwuzlaFloatingPointFormula(pTerm);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      Long pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    assert getFormulaType(pTerm).isArrayType()
        : "Unexpected formula type for array formula: " + getFormulaType(pTerm);
    return new BitwuzlaArrayFormula<>(pTerm, pIndexType, pElementType);
  }

  @Override
  public Long makeVariable(Long pSort, String varName) {
    Long maybeFormula = formulaCache.get(varName, pSort);
    if (maybeFormula != null) {
      return maybeFormula;
    }

    long newVar = BitwuzlaJNI.bitwuzla_mk_const(pSort, varName);
    formulaCache.put(varName, pSort, newVar);
    return newVar;
  }

  public long makeBoundVariable(long var) {
    String name = BitwuzlaJNI.bitwuzla_term_get_symbol(var);
    Long sort = BitwuzlaJNI.bitwuzla_term_get_sort(var);
    // TODO: do we need a bound cache?
    // Long maybeVar = boundFormulaCache.get(name, sort);
    // if (maybeVar != null) {
    // return maybeVar;
    // }

    long newVar = BitwuzlaJNI.bitwuzla_mk_var(sort, name);
    // boundFormulaCache.put(name, sort, newVar);
    return newVar;
  }

  public FormulaType<?> bitwuzlaSortToType(Long pSort) {
    // UFs play by different rules. For them, we need to extract the domain
    if (BitwuzlaJNI.bitwuzla_sort_is_fp(pSort)) {
      long exponent = BitwuzlaJNI.bitwuzla_sort_fp_get_exp_size(pSort);
      long mantissa = BitwuzlaJNI.bitwuzla_sort_fp_get_sig_size(pSort) - 1;
      return FormulaType.getFloatingPointType((int) exponent, (int) mantissa);
    } else if (BitwuzlaJNI.bitwuzla_sort_is_bv(pSort)) {
      return FormulaType.getBitvectorTypeWithSize(
          (int) BitwuzlaJNI.bitwuzla_sort_bv_get_size(pSort));
    } else if (BitwuzlaJNI.bitwuzla_sort_is_array(pSort)) {
      FormulaType<?> domainSort =
          bitwuzlaSortToType(BitwuzlaJNI.bitwuzla_sort_array_get_element(pSort));
      FormulaType<?> rangeSort =
          bitwuzlaSortToType(BitwuzlaJNI.bitwuzla_sort_array_get_index(pSort));
      return FormulaType.getArrayType(domainSort, rangeSort);
    } else if (BitwuzlaJNI.bitwuzla_sort_is_bool(pSort)) {
      return FormulaType.BooleanType;
    } else if (BitwuzlaJNI.bitwuzla_sort_is_rm(pSort)) {
      return FormulaType.FloatingPointRoundingModeType;
    }

    throw new UnsupportedOperationException(
        "Could not find the JavaSMT type for sort"
            + BitwuzlaJNI.bitwuzla_sort_to_string(pSort)
            + ".");
  }

  private FunctionDeclarationKind getDeclarationKind(Long term) {
    BitwuzlaKind kind = BitwuzlaKind.swigToEnum(BitwuzlaJNI.bitwuzla_term_get_kind(term));

    if (kind.equals(BITWUZLA_KIND_AND)) {
      return FunctionDeclarationKind.AND;
    } else if (kind.equals(BITWUZLA_KIND_DISTINCT)) {
      return FunctionDeclarationKind.DISTINCT;
    } else if (kind.equals(BITWUZLA_KIND_EQUAL)) {
      return FunctionDeclarationKind.EQ;
    } else if (kind.equals(BITWUZLA_KIND_IFF)) {
      return FunctionDeclarationKind.IFF;
    } else if (kind.equals(BITWUZLA_KIND_IMPLIES)) {
      return FunctionDeclarationKind.IMPLIES;
    } else if (kind.equals(BITWUZLA_KIND_NOT)) {
      return FunctionDeclarationKind.NOT;
    } else if (kind.equals(BITWUZLA_KIND_OR)) {
      return FunctionDeclarationKind.OR;
    } else if (kind.equals(BITWUZLA_KIND_XOR)) {
      return FunctionDeclarationKind.XOR;
    } else if (kind.equals(BITWUZLA_KIND_ITE)) {
      return FunctionDeclarationKind.ITE;
    } else if (kind.equals(BITWUZLA_KIND_APPLY)) {
      return FunctionDeclarationKind.UF;
    } else if (kind.equals(BITWUZLA_KIND_ARRAY_SELECT)) {
      return FunctionDeclarationKind.SELECT;
    } else if (kind.equals(BITWUZLA_KIND_ARRAY_STORE)) {
      return FunctionDeclarationKind.STORE;
    } else if (kind.equals(BITWUZLA_KIND_BV_ADD)) {
      return FunctionDeclarationKind.BV_ADD;
    } else if (kind.equals(BITWUZLA_KIND_BV_AND)) {
      return FunctionDeclarationKind.BV_AND;
    } else if (kind.equals(BITWUZLA_KIND_BV_ASHR)) {
      return FunctionDeclarationKind.BV_ASHR;
    } else if (kind.equals(BITWUZLA_KIND_BV_CONCAT)) {
      return FunctionDeclarationKind.BV_CONCAT;
    } else if (kind.equals(BITWUZLA_KIND_BV_SMOD)) {
      return FunctionDeclarationKind.BV_SMOD;
    } else if (kind.equals(BITWUZLA_KIND_BV_MUL)) {
      return FunctionDeclarationKind.BV_MUL;
    } else if (kind.equals(BITWUZLA_KIND_BV_NEG)) {
      return FunctionDeclarationKind.BV_NEG;
    } else if (kind.equals(BITWUZLA_KIND_BV_NOT)) {
      return FunctionDeclarationKind.BV_NOT;
    } else if (kind.equals(BITWUZLA_KIND_BV_OR)) {
      return FunctionDeclarationKind.BV_OR;
    } else if (kind.equals(BITWUZLA_KIND_BV_SDIV)) {
      return FunctionDeclarationKind.BV_SDIV;
    } else if (kind.equals(BITWUZLA_KIND_BV_SGE)) {
      return FunctionDeclarationKind.BV_SGE;
    } else if (kind.equals(BITWUZLA_KIND_BV_SGT)) {
      return FunctionDeclarationKind.BV_SGT;
    } else if (kind.equals(BITWUZLA_KIND_BV_SHL)) {
      return FunctionDeclarationKind.BV_SHL;
    } else if (kind.equals(BITWUZLA_KIND_BV_SLE)) {
      return FunctionDeclarationKind.BV_SLE;
    } else if (kind.equals(BITWUZLA_KIND_BV_SLT)) {
      return FunctionDeclarationKind.BV_SLT;
    } else if (kind.equals(BITWUZLA_KIND_BV_SREM)) {
      return FunctionDeclarationKind.BV_SREM;
    } else if (kind.equals(BITWUZLA_KIND_BV_SUB)) {
      return FunctionDeclarationKind.BV_SUB;
    } else if (kind.equals(BITWUZLA_KIND_BV_UDIV)) {
      return FunctionDeclarationKind.BV_UDIV;
    } else if (kind.equals(BITWUZLA_KIND_BV_UGE)) {
      return FunctionDeclarationKind.BV_UGE;
    } else if (kind.equals(BITWUZLA_KIND_BV_UGT)) {
      return FunctionDeclarationKind.BV_UGT;
    } else if (kind.equals(BITWUZLA_KIND_BV_ULE)) {
      return FunctionDeclarationKind.BV_ULE;
    } else if (kind.equals(BITWUZLA_KIND_BV_ULT)) {
      return FunctionDeclarationKind.BV_ULT;
    } else if (kind.equals(BITWUZLA_KIND_BV_UREM)) {
      return FunctionDeclarationKind.BV_UREM;
    } else if (kind.equals(BITWUZLA_KIND_BV_EXTRACT)) {
      return FunctionDeclarationKind.BV_EXTRACT;
    } else if (kind.equals(BITWUZLA_KIND_BV_SIGN_EXTEND)) {
      return FunctionDeclarationKind.BV_SIGN_EXTENSION;
    } else if (kind.equals(BITWUZLA_KIND_BV_ZERO_EXTEND)) {
      return FunctionDeclarationKind.BV_ZERO_EXTENSION;
    } else if (kind.equals(BITWUZLA_KIND_FP_ABS)) {
      return FunctionDeclarationKind.FP_ABS;
    } else if (kind.equals(BITWUZLA_KIND_FP_ADD)) {
      return FunctionDeclarationKind.FP_ADD;
    } else if (kind.equals(BITWUZLA_KIND_FP_DIV)) {
      return FunctionDeclarationKind.FP_DIV;
    } else if (kind.equals(BITWUZLA_KIND_FP_EQUAL)) {
      return FunctionDeclarationKind.FP_EQ;
    } else if (kind.equals(BITWUZLA_KIND_FP_GEQ)) {
      return FunctionDeclarationKind.FP_GE;
    } else if (kind.equals(BITWUZLA_KIND_FP_GT)) {
      return FunctionDeclarationKind.FP_GT;
    } else if (kind.equals(BITWUZLA_KIND_FP_IS_INF)) {
      return FunctionDeclarationKind.FP_IS_INF;
    } else if (kind.equals(BITWUZLA_KIND_FP_IS_NAN)) {
      return FunctionDeclarationKind.FP_IS_NAN;
    } else if (kind.equals(BITWUZLA_KIND_FP_IS_NEG)) {
      return FunctionDeclarationKind.FP_IS_NEGATIVE;
    } else if (kind.equals(BITWUZLA_KIND_FP_IS_NORMAL)) {
      return FunctionDeclarationKind.FP_IS_NORMAL;
    } else if (kind.equals(BITWUZLA_KIND_FP_IS_SUBNORMAL)) {
      return FunctionDeclarationKind.FP_IS_SUBNORMAL;
    } else if (kind.equals(BITWUZLA_KIND_FP_IS_ZERO)) {
      return FunctionDeclarationKind.FP_IS_ZERO;
    } else if (kind.equals(BITWUZLA_KIND_FP_LEQ)) {
      return FunctionDeclarationKind.FP_LE;
    } else if (kind.equals(BITWUZLA_KIND_FP_LT)) {
      return FunctionDeclarationKind.FP_LT;
    } else if (kind.equals(BITWUZLA_KIND_FP_MAX)) {
      return FunctionDeclarationKind.FP_MAX;
    } else if (kind.equals(BITWUZLA_KIND_FP_MIN)) {
      return FunctionDeclarationKind.FP_MIN;
    } else if (kind.equals(BITWUZLA_KIND_FP_MUL)) {
      return FunctionDeclarationKind.FP_MUL;
    } else if (kind.equals(BITWUZLA_KIND_FP_NEG)) {
      return FunctionDeclarationKind.FP_NEG;
    } else if (kind.equals(BITWUZLA_KIND_FP_RTI)) {
      return FunctionDeclarationKind.FP_ROUND_TO_INTEGRAL;
    } else if (kind.equals(BITWUZLA_KIND_FP_SQRT)) {
      return FunctionDeclarationKind.FP_SQRT;
    } else if (kind.equals(BITWUZLA_KIND_FP_SUB)) {
      return FunctionDeclarationKind.FP_SUB;
    } else if (kind.equals(BITWUZLA_KIND_FP_TO_FP_FROM_BV)) {
      return FunctionDeclarationKind.BV_UCASTTO_FP;
    } else if (kind.equals(BITWUZLA_KIND_FP_TO_FP_FROM_FP)) {
      return FunctionDeclarationKind.FP_CASTTO_FP;
    } else if (kind.equals(BITWUZLA_KIND_FP_TO_FP_FROM_SBV)) {
      return FunctionDeclarationKind.BV_SCASTTO_FP;
    } else if (kind.equals(BITWUZLA_KIND_FP_TO_FP_FROM_UBV)) {
      return FunctionDeclarationKind.BV_UCASTTO_FP;
    } else if (kind.equals(BITWUZLA_KIND_FP_TO_SBV)) {
      return FunctionDeclarationKind.FP_CASTTO_SBV;
    } else if (kind.equals(BITWUZLA_KIND_FP_TO_UBV)) {
      return FunctionDeclarationKind.FP_CASTTO_UBV;
    } else if (kind.equals(BITWUZLA_KIND_BV_XOR)) {
      return FunctionDeclarationKind.BV_XOR;
    }
    throw new UnsupportedOperationException("Can not discern formula kind " + kind);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, Long pTerm) {
    assert pType.equals(getFormulaType(pTerm))
        : String.format(
            "Trying to encapsulate formula of type %s as %s", getFormulaType(pTerm), pType);
    if (pType.isBooleanType()) {
      return (T) new BitwuzlaBooleanFormula(pTerm);
    } else if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrFt = (ArrayFormulaType<?, ?>) pType;
      return (T) new BitwuzlaArrayFormula<>(pTerm, arrFt.getIndexType(), arrFt.getElementType());
    } else if (pType.isBitvectorType()) {
      return (T) new BitwuzlaBitvectorFormula(pTerm);
    } else if (pType.isFloatingPointType()) {
      return (T) new BitwuzlaFloatingPointFormula(pTerm);
    } else if (pType.isFloatingPointRoundingModeType()) {
      return (T) new BitwuzlaFloatingPointRoundingModeFormula(pTerm);
    }
    throw new IllegalArgumentException("Cannot create formulas of type " + pType + " in Bitwuzla");
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    long sort = BitwuzlaJNI.bitwuzla_term_get_sort(extractInfo(pFormula));
    if (pFormula instanceof BitvectorFormula) {
      checkArgument(
          BitwuzlaJNI.bitwuzla_sort_is_bv(sort),
          "BitvectorFormula with type missmatch: %s",
          pFormula);
      return (FormulaType<T>)
          FormulaType.getBitvectorTypeWithSize(
              Math.toIntExact(BitwuzlaJNI.bitwuzla_sort_bv_get_size(sort)));
    } else if (pFormula instanceof ArrayFormula<?, ?>) {
      FormulaType<T> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<T, T>) pFormula);
      FormulaType<T> arrayElementType = getArrayFormulaElementType((ArrayFormula<T, T>) pFormula);
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    } else if (pFormula instanceof FloatingPointFormula) {
      if (!BitwuzlaJNI.bitwuzla_sort_is_fp(sort)) {
        throw new IllegalArgumentException(
            "FloatingPointFormula with actual type "
                + BitwuzlaJNI.bitwuzla_sort_to_string(sort)
                + ": "
                + pFormula);
      }
      int exp = (int) BitwuzlaJNI.bitwuzla_sort_fp_get_exp_size(sort);
      int man = (int) BitwuzlaJNI.bitwuzla_sort_fp_get_sig_size(sort) - 1;
      return (FormulaType<T>) FormulaType.getFloatingPointType(exp, man);
    } else if (BitwuzlaJNI.bitwuzla_sort_is_rm(sort)) {
      return (FormulaType<T>) FormulaType.FloatingPointRoundingModeType;
    }
    return super.getFormulaType(pFormula);
  }

  @Override
  public FormulaType<?> getFormulaType(Long formula) {
    long pType = BitwuzlaJNI.bitwuzla_term_get_sort(formula);
    return bitwuzlaSortToType(pType);
  }

  private BigDecimal parseIEEEbinaryFP(long pTerm) {
    // The Bitwuzla string for FPs is always in binary, regardless of the second argument.

    String fp = BitwuzlaJNI.bitwuzla_term_value_get_str(pTerm);

    if (fp.length() == 32) {
      float result = Float.intBitsToFloat(Integer.parseUnsignedInt(fp, 2));
      return new BigDecimal(result);
    } else if (fp.length() == 64) {
      double result = Double.longBitsToDouble(Long.parseUnsignedLong(fp, 2));
      return new BigDecimal(result);
    } else {
      throw new UnsupportedOperationException(
          "Visitor can only visit constant FPs of 32 or 64 " + "bits.");
    }

    //    String fpSMTLIB = bitwuzlaJNI.bitwuzla_term_to_string(pTerm);
    //    String[] mySplit = fpSMTLIB.split(" #b");
    //    mySplit[3] = mySplit[3].replace(")", "");
    //    double result = calculateDecimal(mySplit[3], mySplit[2], mySplit[1]);
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, Long f)
      throws UnsupportedOperationException {
    BitwuzlaKind kind = BitwuzlaKind.swigToEnum(BitwuzlaJNI.bitwuzla_term_get_kind(f));
    if (termIsConstant(f)) {
      return visitor.visitConstant(formula, convertValue(f));

    } else if (BitwuzlaJNI.bitwuzla_term_is_fp_value(f)) {
      return visitor.visitConstant(formula, parseIEEEbinaryFP(f));

    } else if (BitwuzlaJNI.bitwuzla_term_is_const(f)) {
      String name = BitwuzlaJNI.bitwuzla_term_get_symbol(f);
      return visitor.visitFreeVariable(formula, name);

    } else if (BitwuzlaJNI.bitwuzla_term_is_var(f)) {
      String name = BitwuzlaJNI.bitwuzla_term_get_symbol(f);
      long sort = BitwuzlaJNI.bitwuzla_term_get_sort(f);
      long originalVar = formulaCache.get(name, sort);
      return visitor.visitBoundVariable(encapsulate(getFormulaType(originalVar), originalVar), 0);

    } else if (kind.equals(BITWUZLA_KIND_EXISTS) || kind.equals(BITWUZLA_KIND_FORALL)) {
      long[] children = BitwuzlaJNI.bitwuzla_term_get_children(f, new long[1]);
      // QUANTIFIER: replace bound variable with free variable for visitation
      int size = children.length;
      assert children.length == 2;
      long bodyUnSub = children[size - 1];
      List<Formula> freeEncVars = new ArrayList<>();
      // The first length - 2 elements are bound vars, and the last element is the body
      long[] boundVars = new long[size - 1];
      long[] freeVars = new long[size - 1];
      for (int i = 0; i < size - 1; i++) {
        long boundVar = children[i];
        boundVars[i] = boundVar;
        String name = BitwuzlaJNI.bitwuzla_term_get_symbol(boundVar);
        assert name != null;
        long sort = BitwuzlaJNI.bitwuzla_term_get_sort(boundVar);
        long freeVar;
        if (formulaCache.contains(name, sort)) {
          freeVar = formulaCache.get(name, sort);
        } else {
          // no free var existing (e.g. from parsing), create a new one
          freeVar = makeVariable(sort, name);
        }
        freeVars[i] = freeVar;
        freeEncVars.add(encapsulate(getFormulaType(freeVar), freeVar));
      }

      long bodySubbed = BitwuzlaJNI.bitwuzla_substitute_term(bodyUnSub, 1, boundVars, freeVars);

      Quantifier quant = kind.equals(BITWUZLA_KIND_EXISTS) ? Quantifier.EXISTS : Quantifier.FORALL;
      return visitor.visitQuantifier(
          (BooleanFormula) formula, quant, freeEncVars, encapsulateBoolean(bodySubbed));

    } else {
      long[] args = BitwuzlaJNI.bitwuzla_term_get_children(f, new long[1]);
      ImmutableList.Builder<Formula> arguments = ImmutableList.builder();
      ImmutableList.Builder<FormulaType<?>> argumentTypes = ImmutableList.builder();

      String name = BitwuzlaJNI.bitwuzla_term_get_symbol(f);

      BitwuzlaDeclaration decl = null;
      for (int i = 0; i < args.length; i++) {
        long argument = args[i];
        if (kind == BITWUZLA_KIND_APPLY && i == 0) {
          // UFs carry the decl in the first child and the decl has the name
          decl = new BitwuzlaDeclaration(argument, false);
          name = BitwuzlaJNI.bitwuzla_term_get_symbol(argument);
          continue;
        }
        FormulaType<?> type = getFormulaType(argument);
        arguments.add(encapsulate(type, argument));
        argumentTypes.add(type);
      }

      if (name == null) {
        name = BitwuzlaJNI.bitwuzla_kind_to_string(BitwuzlaJNI.bitwuzla_term_get_kind(f));
      }
      if (decl == null) {
        decl = new BitwuzlaDeclaration(BitwuzlaJNI.bitwuzla_term_get_kind(f), true);
      }
      if (BitwuzlaJNI.bitwuzla_term_is_indexed(f)) {
        // We need to retain the original formula as the declaration for indexed formulas,
        // otherwise we loose the index info, but we also need to know if its a kind or term
        decl = new BitwuzlaDeclaration(f, false);
      }

      return visitor.visitFunction(
          formula,
          arguments.build(),
          FunctionDeclarationImpl.of(
              name, getDeclarationKind(f), argumentTypes.build(), getFormulaType(f), decl));
    }
  }

  private boolean termIsConstant(long term) {
    return BITWUZLA_KIND_VALUE.swigValue() == BitwuzlaJNI.bitwuzla_term_get_kind(term);
  }

  @Override
  public Long callFunctionImpl(BitwuzlaDeclaration declaration, List<Long> args) {
    // For UFs the declaration needs to be a const wrapping of the function sort
    // For all other functions it needs to be the kind
    // BUT, we can never use a bitwuzla_term_is... function on a KIND
    if (!declaration.isKind() && BitwuzlaJNI.bitwuzla_term_is_indexed(declaration.getTerm())) {
      // The term might be indexed, then we need index creation
      long term = declaration.getTerm();
      int properKind = BitwuzlaJNI.bitwuzla_term_get_kind(term);
      if (BitwuzlaKind.swigToEnum(properKind) == BITWUZLA_KIND_BV_ZERO_EXTEND) {
        System.out.println();
      }
      long[] indices = BitwuzlaJNI.bitwuzla_term_get_indices(term, new long[1]);
      return BitwuzlaJNI.bitwuzla_mk_term_indexed(
          properKind,
          args.size(),
          args.stream().mapToLong(Long::longValue).toArray(),
          indices.length,
          indices);
    }

    if (!declaration.isKind() && BitwuzlaJNI.bitwuzla_term_is_fun(declaration.getTerm())) {
      long[] functionAndArgs =
          LongStream.concat(
                  LongStream.of(declaration.getTerm()), args.stream().mapToLong(Long::longValue))
              .toArray();
      return BitwuzlaJNI.bitwuzla_mk_term(
          BITWUZLA_KIND_APPLY.swigValue(), functionAndArgs.length, functionAndArgs);
    }

    assert declaration.isKind();
    long declKind = declaration.getKind();

    return BitwuzlaJNI.bitwuzla_mk_term(
        (int) declKind, args.size(), args.stream().mapToLong(Long::longValue).toArray());
  }

  @Override
  public BitwuzlaDeclaration declareUFImpl(String name, Long pReturnType, List<Long> pArgTypes) {
    if (pArgTypes.isEmpty()) {
      // Bitwuzla does not support UFs with no args, so we make a variable
      // TODO: implement
      throw new UnsupportedOperationException("Bitwuzla does not support 0 arity UFs.");
    }
    long functionSort =
        BitwuzlaJNI.bitwuzla_mk_fun_sort(
            pArgTypes.size(), pArgTypes.stream().mapToLong(Long::longValue).toArray(), pReturnType);

    Long maybeFormula = formulaCache.get(name, functionSort);
    if (maybeFormula != null) {
      return new BitwuzlaDeclaration(maybeFormula, false);
    }

    long uf = BitwuzlaJNI.bitwuzla_mk_const(functionSort, name);
    formulaCache.put(name, functionSort, uf);
    return new BitwuzlaDeclaration(uf, false);
  }

  @Override
  protected BitwuzlaDeclaration getBooleanVarDeclarationImpl(Long pLong) {
    long kind = BitwuzlaJNI.bitwuzla_term_get_kind(pLong);

    // CONSTANTS are "variables" and Kind.VARIABLES are bound variables in for example quantifiers
    assert kind == BITWUZLA_KIND_APPLY.swigValue() || kind == BITWUZLA_KIND_CONSTANT.swigValue()
        : BitwuzlaJNI.bitwuzla_term_to_string(kind);
    if (kind == BITWUZLA_KIND_APPLY.swigValue()) {
      long[] size = new long[1];
      long[] pChildren = BitwuzlaJNI.bitwuzla_term_get_children(pLong, size);
      // Returns pointer to Uninterpreted Function used in Apply
      return new BitwuzlaDeclaration(pChildren[0], false);
    } else {
      return new BitwuzlaDeclaration(pLong, true);
    }
  }

  @Override
  public Long extractInfo(Formula pT) {
    return BitwuzlaFormulaManager.getBitwuzlaTerm(pT);
  }

  @Override
  public BooleanFormula encapsulateBoolean(Long pTerm) {
    assert getFormulaType(pTerm).isBooleanType();
    return new BitwuzlaBooleanFormula(pTerm);
  }

  protected Table<String, Long, Long> getCache() {
    return formulaCache;
  }

  // True if the entered String has an existing variable in the cache.
  protected boolean formulaCacheContains(String variable) {
    // There is always only 1 type permitted per variable
    return formulaCache.containsRow(variable);
  }

  // Optional that contains the variable to the entered String if there is one.
  protected Optional<Long> getFormulaFromCache(String variable) {
    Iterator<Entry<Long, Long>> entrySetIter = formulaCache.row(variable).entrySet().iterator();
    if (entrySetIter.hasNext()) {
      // If there is a non empty row for an entry, there is only one entry
      return Optional.of(entrySetIter.next().getValue());
    }
    return Optional.empty();
  }

  @Override
  public Object convertValue(Long term) {
    String value;
    long sort = BitwuzlaJNI.bitwuzla_term_get_sort(term);
    if (BitwuzlaJNI.bitwuzla_term_is_const(term)) {
      return null;
    }
    if (BitwuzlaJNI.bitwuzla_sort_is_fun(sort)) {
      // TODO: this is wrong
      throw new AssertionError("Error: Unknown sort and term");
    } else {
      value = BitwuzlaJNI.bitwuzla_term_to_string(term);
      if (value.startsWith("#b")) {
        // Bitvectors in Bitwuzla start with a #b
        return new BigInteger(value.substring(2), 2);
      } else if (value.equals("true")) {
        return true;
      } else if (value.equals("false")) {
        return false;
      } else if (value.startsWith("(fp")) {
        return value
            .replace("(fp", "")
            .replace(")", "")
            .replace("#b", "")
            .replace("#b", "")
            .replace("#b", "")
            .strip();
      } else if (BitwuzlaJNI.bitwuzla_sort_is_rm(sort)) {
        return value;
      }
    }

    throw new AssertionError(
        "Error: Could not convert term to value; Unknown sort and term. "
            + "Value: "
            + BitwuzlaJNI.bitwuzla_term_to_string(term));
  }
}
