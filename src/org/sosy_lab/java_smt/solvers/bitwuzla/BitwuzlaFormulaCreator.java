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

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.*;

import com.google.common.base.Splitter;
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
import java.util.stream.Collectors;
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

public class BitwuzlaFormulaCreator extends FormulaCreator<Long, Long, Long, Long> {
  private final Table<String, Long, Long> formulaCache = HashBasedTable.create();

  protected BitwuzlaFormulaCreator(Long pBitwuzlaEnv) {
    super(pBitwuzlaEnv, bitwuzlaJNI.bitwuzla_mk_bool_sort(), null, null, null, null);
  }

  @Override
  public Long getBitvectorType(int bitwidth) {
    return bitwuzlaJNI.bitwuzla_mk_bv_sort(bitwidth);
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
        bitwuzlaJNI.bitwuzla_mk_fp_sort(type.getExponentSize(), type.getMantissaSize() + 1);
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
    return bitwuzlaJNI.bitwuzla_mk_array_sort(indexType, elementType);
  }

  @Override
  protected FloatingPointFormula encapsulateFloatingPoint(Long pTerm) {
    assert getFormulaType(pTerm).isFloatingPointType()
        : String.format(
            "%s is no FP, but %s (%s)",
            pTerm, bitwuzlaJNI.bitwuzla_term_get_sort(pTerm), getFormulaType(pTerm));
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
    if (formulaCache.containsRow(varName)) {
      throw new IllegalArgumentException("Symbol already used: " + varName);
    }
    long newVar = bitwuzlaJNI.bitwuzla_mk_const(pSort, varName);
    formulaCache.put(varName, pSort, newVar);
    return newVar;
  }

  public FormulaType<?> bitwuzlaSortToType(Long pSort) {
    // UFs play by different rules. For them, we need to extract the domain
    if (bitwuzlaJNI.bitwuzla_sort_is_fp(pSort)) {
      long exponent = bitwuzlaJNI.bitwuzla_sort_fp_get_exp_size(pSort);
      long mantissa = bitwuzlaJNI.bitwuzla_sort_fp_get_sig_size(pSort) - 1;
      return FormulaType.getFloatingPointType((int) exponent, (int) mantissa);
    } else if (bitwuzlaJNI.bitwuzla_sort_is_bv(pSort)) {
      return FormulaType.getBitvectorTypeWithSize(
          (int) bitwuzlaJNI.bitwuzla_sort_bv_get_size(pSort));
    } else if (bitwuzlaJNI.bitwuzla_sort_is_array(pSort)) {
      FormulaType<?> domainSort =
          bitwuzlaSortToType(bitwuzlaJNI.bitwuzla_sort_array_get_element(pSort));
      FormulaType<?> rangeSort =
          bitwuzlaSortToType(bitwuzlaJNI.bitwuzla_sort_array_get_index(pSort));
      return FormulaType.getArrayType(domainSort, rangeSort);
    } else if (bitwuzlaJNI.bitwuzla_sort_is_bool(pSort)) {
      return FormulaType.BooleanType;
    } else if (bitwuzlaJNI.bitwuzla_sort_is_rm(pSort)) {
      return FormulaType.FloatingPointRoundingModeType;
    }

    throw new UnsupportedOperationException(
        "Could not find the JavaSMT type for sort"
            + bitwuzlaJNI.bitwuzla_sort_to_string(pSort)
            + ".");
  }

  private FunctionDeclarationKind getDeclarationKind(Long term) {
    BitwuzlaKind kind = BitwuzlaKind.swigToEnum(bitwuzlaJNI.bitwuzla_term_get_kind(term));

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
    } else if (kind.equals(BITWUZLA_KIND_FP_REM)) {
      // return FunctionDeclarationKind.BV_UREM;
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
    }
    throw new UnsupportedOperationException("Can not discern formula kind " + kind.toString());
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
    long sort = bitwuzlaJNI.bitwuzla_term_get_sort(extractInfo(pFormula));
    if (pFormula instanceof BitvectorFormula) {
      checkArgument(
          bitwuzlaJNI.bitwuzla_sort_is_bv(sort),
          "BitvectorFormula with type missmatch: %s",
          pFormula);
      return (FormulaType<T>)
          FormulaType.getBitvectorTypeWithSize(
              Math.toIntExact(bitwuzlaJNI.bitwuzla_sort_bv_get_size(sort)));
    } else if (pFormula instanceof ArrayFormula<?, ?>) {
      FormulaType<T> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<T, T>) pFormula);
      FormulaType<T> arrayElementType = getArrayFormulaElementType((ArrayFormula<T, T>) pFormula);
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    } else if (pFormula instanceof FloatingPointFormula) {
      if (!bitwuzlaJNI.bitwuzla_sort_is_fp(sort)) {
        throw new IllegalArgumentException(
            "FloatingPointFormula with actual type "
                + bitwuzlaJNI.bitwuzla_sort_to_string(sort)
                + ": "
                + pFormula);
      }
      int exp = (int) bitwuzlaJNI.bitwuzla_sort_fp_get_exp_size(sort);
      int man = (int) bitwuzlaJNI.bitwuzla_sort_fp_get_sig_size(sort) - 1;
      return (FormulaType<T>) FormulaType.getFloatingPointType(exp, man);
    } else if (bitwuzlaJNI.bitwuzla_sort_is_rm(sort)) {
      return (FormulaType<T>) FormulaType.FloatingPointRoundingModeType;
    }
    return super.getFormulaType(pFormula);
  }

  @Override
  public FormulaType<?> getFormulaType(Long formula) {
    long pType = bitwuzlaJNI.bitwuzla_term_get_sort(formula);
    return bitwuzlaSortToType(pType);
  }

  private BigDecimal parseIEEEbinaryFP(long pTerm) {
    // The Bitwuzla string for FPs is always in binary, regardless of the second argument.

    String fp = bitwuzlaJNI.bitwuzla_term_value_get_str(pTerm);

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
    BitwuzlaKind kind = BitwuzlaKind.swigToEnum(bitwuzlaJNI.bitwuzla_term_get_kind(f));
    if (termIsConstant(f)) {
      return visitor.visitConstant(formula, convertValue(f));
    } else if (bitwuzlaJNI.bitwuzla_term_is_fp_value(f)) {
      return visitor.visitConstant(formula, parseIEEEbinaryFP(f));
    } else if (bitwuzlaJNI.bitwuzla_term_is_const(f)) {
      String name = bitwuzlaJNI.bitwuzla_term_get_symbol(f);
      return visitor.visitFreeVariable(formula, name);
    } else if (bitwuzlaJNI.bitwuzla_term_is_var(f)) {
      return visitor.visitBoundVariable(formula, 0);
    } else if (kind.equals(BITWUZLA_KIND_EXISTS) || kind.equals(BITWUZLA_KIND_FORALL)) {
      long[] pSize = new long[1];
      long[] pChildren = bitwuzlaJNI.bitwuzla_term_get_children(f, pSize);
      long size = pSize[0];
      // QUANTIFIER: replace bound variable with free variable for visitation
      assert size == 2;
      assert pChildren.length == 2;
      long bodyUnSub = pChildren[1];
      List<Formula> freeVars = new ArrayList<>();
      // Only unpacking one level of quantifier at a time, which always only tracks one bound var.
      long[] boundVar = {pChildren[0]};
      String name = bitwuzlaJNI.bitwuzla_term_get_symbol(boundVar[0]);
      assert name != null;
      long sort = bitwuzlaJNI.bitwuzla_term_get_sort(boundVar[0]);

      // Why get from cache?
      // long freeVar = Preconditions.checkNotNull(formulaCache.get(name, sort));
      long[] freeVar = {bitwuzlaJNI.bitwuzla_mk_const(sort, name)};

      long bodySubbed = bitwuzlaJNI.bitwuzla_substitute_term(bodyUnSub, 1, boundVar, freeVar);

      BooleanFormula fBody = encapsulateBoolean(bodySubbed);
      Quantifier quant = kind.equals(BITWUZLA_KIND_EXISTS) ? Quantifier.EXISTS : Quantifier.FORALL;
      return visitor.visitQuantifier((BooleanFormula) formula, quant, freeVars, fBody);
    } else {
      long[] args = bitwuzlaJNI.bitwuzla_term_get_children(f, new long[1]);
      ImmutableList.Builder<Formula> arguments = ImmutableList.builder();
      ImmutableList.Builder<FormulaType<?>> argumentTypes = ImmutableList.builder();

      String name = bitwuzlaJNI.bitwuzla_term_get_symbol(f);

      Long decl = null;
      for (int i = 0; i < args.length; i++) {
        long argument = args[i];
        if (kind == BITWUZLA_KIND_APPLY && i == 0) {
          // UFs carry the decl in the first child and the decl has the name
          decl = argument;
          name = bitwuzlaJNI.bitwuzla_term_get_symbol(argument);
          continue;
        }
        FormulaType<?> type = getFormulaType(argument);
        arguments.add(encapsulate(type, argument));
        argumentTypes.add(type);
      }

      if (name == null) {
        name = bitwuzlaJNI.bitwuzla_kind_to_string(bitwuzlaJNI.bitwuzla_term_get_kind(f));
      }
      if (decl == null) {
        decl = (long) bitwuzlaJNI.bitwuzla_term_get_kind(f);
      }

      return visitor.visitFunction(
          formula,
          arguments.build(),
          FunctionDeclarationImpl.of(
              name, getDeclarationKind(f), argumentTypes.build(), getFormulaType(f), decl));
    }
  }

  private boolean termIsConstant(long term) {
    return BITWUZLA_KIND_VALUE.swigValue() == bitwuzlaJNI.bitwuzla_term_get_kind(term);
  }

  @Override
  public Long callFunctionImpl(Long declaration, List<Long> args) {
    long[] functionAndArgs =
        LongStream.concat(LongStream.of(declaration), args.stream().mapToLong(Long::longValue))
            .toArray();
    return bitwuzlaJNI.bitwuzla_mk_term(
        BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue(), functionAndArgs.length, functionAndArgs);
  }

  @Override
  public Long declareUFImpl(String name, Long pReturnType, List<Long> pArgTypes) {
    long functionSort =
        bitwuzlaJNI.bitwuzla_mk_fun_sort(
            pArgTypes.size(), pArgTypes.stream().mapToLong(Long::longValue).toArray(), pReturnType);

    Long maybeFormula = formulaCache.get(name, functionSort);
    if (maybeFormula != null) {
      return maybeFormula;
    }
    if (formulaCache.containsRow(name)) {
      throw new IllegalArgumentException("Symbol already used: " + name);
    }
    long uf = bitwuzlaJNI.bitwuzla_mk_const(functionSort, name);
    formulaCache.put(name, functionSort, uf);
    return uf;
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(Long pLong) {
    long kind = bitwuzlaJNI.bitwuzla_term_get_kind(pLong);

    // CONSTANTS are "variables" and Kind.VARIABLES are bound variables in for example quantifiers
    assert kind == BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue()
            || kind == BITWUZLA_KIND_CONSTANT.swigValue()
        : bitwuzlaJNI.bitwuzla_term_to_string(kind);
    if (kind == BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue()) {
      long[] size = new long[1];
      long[] pChildren = bitwuzlaJNI.bitwuzla_term_get_children(pLong, size);
      // Returns pointer to Uninterpreted Function used in Apply
      return pChildren[0];
    } else {
      return pLong;
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
    long sort = bitwuzlaJNI.bitwuzla_term_get_sort(term);
    if (bitwuzlaJNI.bitwuzla_term_is_const(term)) {
      return null;
    }
    if (bitwuzlaJNI.bitwuzla_sort_is_fun(sort)) {
      // TODO: this is wrong
      throw new AssertionError("Error: Unknown sort and term");
    } else {
      value = bitwuzlaJNI.bitwuzla_term_to_string(term);
      if (value.startsWith("#b")) {
        // Bitvectors in Bitwuzla start with a #b
        return new BigInteger(value.substring(2), 2);
      } else if (value.equals("true")) {
        return true;
      } else if (value.equals("false")) {
        return false;
      } else if (value.startsWith("(fp")) {
        return bigDecimalFromIEEE754FP(term);
      } else if (bitwuzlaJNI.bitwuzla_sort_is_rm(sort)) {
        return value;
      }
    }

    throw new AssertionError(
        "Error: Could not convert term to value; Unknown sort and term. "
            + "Value: "
            + bitwuzlaJNI.bitwuzla_term_to_string(term));
  }

  private BigDecimal bigDecimalFromIEEE754FP(long term) {
    // This is basically impossible to get right in Java.... wait for the methof of the devs
    String value = bitwuzlaJNI.bitwuzla_term_to_string(term);
    // FP of the form: (fp #bx #bxxxx #bxxxxxxxxxx)
    // With x being bitvectors (Signed, exp, mantissa)
    // Strip the (fp and the trailing )
    value = value.substring(3, value.length() - 1);
    // Split by _#b, recieve the 3 BVs
    List<String> values =
        Splitter.on("#b").splitToList(value.trim()).stream()
            .filter(n -> !n.isEmpty())
            .map(n -> n.trim())
            .collect(Collectors.toList());
    int exp = new BigInteger(values.get(1), 2).intValueExact();
    int normalizedExp = exp - ((int) Math.pow(2, (values.get(1).length() - 1))) - 1;
    int man0 = new BigInteger(values.get(2), 2).intValueExact();
    int signBit = new BigInteger(values.get(0), 2).intValueExact();
    if (exp == 0 && man0 == 0) {
      // Special IEEE 754 case for 0
      if (signBit == 1) {
        // -0.0

      }
      return BigDecimal.ZERO;
    }
    // Now build the value
    BigDecimal sign = BigDecimal.valueOf(-1).pow(signBit);
    BigDecimal twoPowNormExp = BigDecimal.valueOf(2).pow(normalizedExp);
    // First remove trailing 0s from mantissa
    String mantissaString = values.get(2);
    for (int i = mantissaString.length() - 1; i < 0; i--) {
      char ch = mantissaString.charAt(i);
      if (ch != 0) {
        break;
      }
      // It is probably better to handle this as a char array
      mantissaString = mantissaString.substring(0, mantissaString.length() - 1);
    }
    // Build mantissa magnitude
    BigDecimal mant = BigDecimal.ZERO;
    for (int i = 0; i < mantissaString.length(); i++) {
      char bit = mantissaString.charAt(i);
      if (bit == '1') {
        mant = mant.add(BigDecimal.valueOf(2).pow(-(i + 1)));
      }
    }
    mant = mant.add(BigDecimal.ONE);
    return sign.multiply(twoPowNormExp).multiply(mant);
  }
}
