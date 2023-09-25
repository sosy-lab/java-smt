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

import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaKind.*;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Table;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.stream.LongStream;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaFormula.BitwuzlaBooleanFormula;

public class BitwuzlaFormulaCreator extends FormulaCreator<Long, Long, Long, Long> {
  private final Table<String, Long, Long> formulaCache = HashBasedTable.create();

  protected BitwuzlaFormulaCreator(Long pBitwuzlaEnv) {
    super(pBitwuzlaEnv, bitwuzlaJNI.bitwuzla_mk_bool_sort(), null, null, null, null);
  }

  @Override
  public Long getBitvectorType(int bitwidth) {
    return bitwuzlaJNI.bitwuzla_mk_bv_sort(bitwidth);
  }

  // Assuming that JavaSMT FloatingPointType follows IEEE 754, if it is in the decimal
  // system instead use bitwuzla_mk_fp_value_from_real somehow or convert myself
  @Override
  public Long getFloatingPointType(FloatingPointType type) {
    long fpSort = bitwuzlaJNI.bitwuzla_mk_fp_sort(type.getExponentSize(), type.getMantissaSize());
    return fpSort;
  }

  @Override
  public Long getArrayType(Long indexType, Long elementType) {
    return bitwuzlaJNI.bitwuzla_mk_array_sort(indexType, elementType);
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

  public FormulaType<? extends Formula> bitwuzlaSortToType(Long pSort) {
    if (bitwuzlaJNI.bitwuzla_sort_is_fp(pSort)) {
      long exponent = bitwuzlaJNI.bitwuzla_sort_fp_get_exp_size(pSort);
      long mantissa = bitwuzlaJNI.bitwuzla_sort_fp_get_sig_size(pSort);
      return FormulaType.getFloatingPointType((int) exponent, (int) mantissa);
    } else if (bitwuzlaJNI.bitwuzla_sort_is_bv(pSort)) {
      return FormulaType.getBitvectorTypeWithSize(
          (int) bitwuzlaJNI.bitwuzla_sort_bv_get_size(pSort));
    } else if (bitwuzlaJNI.bitwuzla_sort_is_array(pSort)) {
      FormulaType<? extends Formula> domainSort =
          bitwuzlaSortToType(bitwuzlaJNI.bitwuzla_term_array_get_index_sort(pSort));
      FormulaType<? extends Formula> rangeSort =
          bitwuzlaSortToType(bitwuzlaJNI.bitwuzla_term_array_get_index_sort(pSort));
      return FormulaType.getArrayType(domainSort, rangeSort);
    } else if (bitwuzlaJNI.bitwuzla_sort_is_rm(pSort)) {
      return FormulaType.FloatingPointRoundingModeType;
    } else {
      throw new UnsupportedOperationException("Unsupported Formulatype.");
    }
  }

  private <R> R visitKind(FormulaVisitor<R> visitor, Formula formula, Long f) {
    BitwuzlaKind kind = BitwuzlaKind.swigToEnum(bitwuzlaJNI.bitwuzla_term_get_kind(f));

    // filled later, except for some special function applications
    String functionName = null;
    List<Formula> functionArgs = new ArrayList<>();
    List<FormulaType<?>> argTypes = new ArrayList<>();

    // filled directly when handling the function application
    FunctionDeclarationKind functionKind = null;
    long[] sizeOutput = new long[1];
    long pfunctionArgs = bitwuzlaJNI.bitwuzla_term_get_children(f, sizeOutput);
    long numberOfArgs = sizeOutput[0];

    if (kind.equals(BITWUZLA_KIND_CONST_ARRAY)) {
      long pArraySort = bitwuzlaJNI.bitwuzla_term_array_get_element_sort(f);
      if (bitwuzlaJNI.bitwuzla_sort_is_bv(pArraySort)) {
        functionKind = FunctionDeclarationKind.BV_CONCAT;
      } else {
        functionKind = FunctionDeclarationKind.OTHER;
      }
    } else if (kind.equals(BITWUZLA_KIND_VARIABLE)) {
      visitor.visitBoundVariable(formula, 0);
    } else if (kind.equals(BITWUZLA_KIND_AND)) {
      functionKind = FunctionDeclarationKind.AND;
    } else if (kind.equals(BITWUZLA_KIND_DISTINCT)) {
      functionKind = FunctionDeclarationKind.DISTINCT;
    } else if (kind.equals(BITWUZLA_KIND_EQUAL)) {
      functionKind = FunctionDeclarationKind.EQ;
    } else if (kind.equals(BITWUZLA_KIND_IFF)) {
      functionKind = FunctionDeclarationKind.IFF;
    } else if (kind.equals(BITWUZLA_KIND_IMPLIES)) {
      functionKind = FunctionDeclarationKind.IMPLIES;
    } else if (kind.equals(BITWUZLA_KIND_NOT)) {
      functionKind = FunctionDeclarationKind.NOT;
    } else if (kind.equals(BITWUZLA_KIND_OR)) {
      functionKind = FunctionDeclarationKind.OR;
    } else if (kind.equals(BITWUZLA_KIND_XOR)) {
      functionKind = FunctionDeclarationKind.XOR;
    } else if (kind.equals(BITWUZLA_KIND_ITE)) {
      functionKind = FunctionDeclarationKind.ITE;
    } else if (kind.equals(BITWUZLA_KIND_EXISTS) || kind.equals(BITWUZLA_KIND_FORALL)) {
      long[] pSize = new long[1];
      long pChildren = bitwuzlaJNI.bitwuzla_term_get_children(f, pSize);
      long size = pSize[0];
      // QUANTIFIER: replace bound variable with free variable for visitation
      assert size == 2;
      long bodyUnSub = bitwuzlaJNI.BitwuzlaTermArray_getitem(pChildren, 1);
      List<Formula> freeVars = new ArrayList<>();
      // Only unpacking one level of quantifier at a time, which always only tracks one bound var.
      long[] boundVar = {bitwuzlaJNI.BitwuzlaTermArray_getitem(pChildren, 0)};
      String name = bitwuzlaJNI.bitwuzla_term_get_symbol(boundVar[0]);
      assert name != null;
      long sort = bitwuzlaJNI.bitwuzla_term_get_sort(boundVar[0]);

      // Why get from cache?
      // long freeVar = Preconditions.checkNotNull(formulaCache.get(name, sort));
      long[] freeVar = {bitwuzlaJNI.bitwuzla_mk_const(sort, name)};

      long bodySubbed =
          bitwuzlaJNI.bitwuzla_substitute_term(getEnv(), bodyUnSub, 1, boundVar, freeVar);

      BooleanFormula fBody = encapsulateBoolean(bodySubbed);
      Quantifier quant = kind.equals(BITWUZLA_KIND_EXISTS) ? Quantifier.EXISTS : Quantifier.FORALL;
      return visitor.visitQuantifier((BooleanFormula) formula, quant, freeVars, fBody);

      //    } else if (kind.equals(BITWUZLA_KIND_FORALL)) {
      //      List<Formula> empty = new ArrayList<>();
      //      visitor.visitQuantifier(
      //          (BooleanFormula) formula,
      //          Quantifier.FORALL,
      //          empty,
      //          encapsulateBoolean(bitwuzlaJNI.BitwuzlaTermArray_getitem(pfunctionArgs, 1)));
    } else if (kind.equals(BITWUZLA_KIND_APPLY)) {
      // TODO Maybe use something different?
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_LAMBDA)) {
      // TODO Maybe use something different?
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_ARRAY_SELECT)) {
      functionKind = FunctionDeclarationKind.SELECT;
    } else if (kind.equals(BITWUZLA_KIND_ARRAY_STORE)) {
      functionKind = FunctionDeclarationKind.STORE;
    } else if (kind.equals(BITWUZLA_KIND_BV_ADD)) {
      functionKind = FunctionDeclarationKind.BV_ADD;
    } else if (kind.equals(BITWUZLA_KIND_BV_AND)) {
      functionKind = FunctionDeclarationKind.BV_AND;
    } else if (kind.equals(BITWUZLA_KIND_BV_ASHR)) {
      functionKind = FunctionDeclarationKind.BV_ASHR;
    } else if (kind.equals(BITWUZLA_KIND_BV_COMP)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_CONCAT)) {
      functionKind = FunctionDeclarationKind.BV_CONCAT;
    } else if (kind.equals(BITWUZLA_KIND_BV_DEC)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_INC)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_MUL)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_NAND)) {
      // Maybe turn into NOT and AND function?
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_NEG)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_NOR)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_NOT)) {
      functionKind = FunctionDeclarationKind.BV_NOT;
    } else if (kind.equals(BITWUZLA_KIND_BV_OR)) {
      functionKind = FunctionDeclarationKind.BV_OR;
    } else if (kind.equals(BITWUZLA_KIND_BV_REDAND)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_REDOR)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_REDXOR)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_ROL)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_ROR)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_SADD_OVERFLOW)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_SDIV_OVERFLOW)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_SDIV)) {
      functionKind = FunctionDeclarationKind.BV_SDIV;
    } else if (kind.equals(BITWUZLA_KIND_BV_SGE)) {
      functionKind = FunctionDeclarationKind.BV_SGE;
    } else if (kind.equals(BITWUZLA_KIND_BV_SGT)) {
      functionKind = FunctionDeclarationKind.BV_SGT;
    } else if (kind.equals(BITWUZLA_KIND_BV_SHL)) {
      functionKind = FunctionDeclarationKind.BV_SHL;
    } else if (kind.equals(BITWUZLA_KIND_BV_SHR)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_SLE)) {
      functionKind = FunctionDeclarationKind.BV_SLE;
    } else if (kind.equals(BITWUZLA_KIND_BV_SLT)) {
      functionKind = FunctionDeclarationKind.BV_SLT;
    } else if (kind.equals(BITWUZLA_KIND_BV_SMOD)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_SMUL_OVERFLOW)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_SREM)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_SSUB_OVERFLOW)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_SUB)) {
      functionKind = FunctionDeclarationKind.BV_SUB;
    } else if (kind.equals(BITWUZLA_KIND_BV_UADD_OVERFLOW)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_UDIV)) {
      functionKind = FunctionDeclarationKind.BV_UDIV;
    } else if (kind.equals(BITWUZLA_KIND_BV_UGE)) {
      functionKind = FunctionDeclarationKind.BV_UGE;
    } else if (kind.equals(BITWUZLA_KIND_BV_UGT)) {
      functionKind = FunctionDeclarationKind.BV_UGT;
    } else if (kind.equals(BITWUZLA_KIND_BV_ULE)) {
      functionKind = FunctionDeclarationKind.BV_ULE;
    } else if (kind.equals(BITWUZLA_KIND_BV_ULT)) {
      functionKind = FunctionDeclarationKind.BV_ULT;
    } else if (kind.equals(BITWUZLA_KIND_BV_UMUL_OVERFLOW)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_UREM)) {
      functionKind = FunctionDeclarationKind.BV_UREM;
    } else if (kind.equals(BITWUZLA_KIND_BV_USUB_OVERFLOW)) {
    } else if (kind.equals(BITWUZLA_KIND_BV_XNOR)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_XOR)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_EXTRACT)) {
      functionKind = FunctionDeclarationKind.BV_EXTRACT;
    } else if (kind.equals(BITWUZLA_KIND_BV_REPEAT)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_ROLI)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_RORI)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_BV_SIGN_EXTEND)) {
      functionKind = FunctionDeclarationKind.BV_SIGN_EXTENSION;
    } else if (kind.equals(BITWUZLA_KIND_BV_ZERO_EXTEND)) {
      functionKind = FunctionDeclarationKind.BV_ZERO_EXTENSION;
    } else if (kind.equals(BITWUZLA_KIND_FP_ABS)) {
      functionKind = FunctionDeclarationKind.FP_ABS;
    } else if (kind.equals(BITWUZLA_KIND_FP_ADD)) {
      functionKind = FunctionDeclarationKind.FP_ADD;
    } else if (kind.equals(BITWUZLA_KIND_FP_DIV)) {
      functionKind = FunctionDeclarationKind.FP_DIV;
    } else if (kind.equals(BITWUZLA_KIND_FP_EQUAL)) {
      functionKind = FunctionDeclarationKind.FP_EQ;
    } else if (kind.equals(BITWUZLA_KIND_FP_FMA)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_FP_FP)) {
    } else if (kind.equals(BITWUZLA_KIND_FP_GEQ)) {
      functionKind = FunctionDeclarationKind.FP_GE;
    } else if (kind.equals(BITWUZLA_KIND_FP_GT)) {
      functionKind = FunctionDeclarationKind.GT;
    } else if (kind.equals(BITWUZLA_KIND_FP_IS_INF)) {
      functionKind = FunctionDeclarationKind.FP_IS_INF;
    } else if (kind.equals(BITWUZLA_KIND_FP_IS_NAN)) {
      functionKind = FunctionDeclarationKind.FP_IS_NAN;
    } else if (kind.equals(BITWUZLA_KIND_FP_IS_NEG)) {
      functionKind = FunctionDeclarationKind.FP_IS_NEGATIVE;
    } else if (kind.equals(BITWUZLA_KIND_FP_IS_NORMAL)) {
      functionKind = FunctionDeclarationKind.FP_IS_NORMAL;
    } else if (kind.equals(BITWUZLA_KIND_FP_IS_POS)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_FP_IS_SUBNORMAL)) {
      functionKind = FunctionDeclarationKind.FP_IS_SUBNORMAL;
    } else if (kind.equals(BITWUZLA_KIND_FP_IS_ZERO)) {
      functionKind = FunctionDeclarationKind.FP_IS_ZERO;
    } else if (kind.equals(BITWUZLA_KIND_FP_LEQ)) {
      functionKind = FunctionDeclarationKind.FP_LE;
    } else if (kind.equals(BITWUZLA_KIND_FP_LT)) {
      functionKind = FunctionDeclarationKind.FP_LT;
    } else if (kind.equals(BITWUZLA_KIND_FP_MAX)) {
      functionKind = FunctionDeclarationKind.FP_MAX;
    } else if (kind.equals(BITWUZLA_KIND_FP_MIN)) {
      functionKind = FunctionDeclarationKind.FP_MIN;
    } else if (kind.equals(BITWUZLA_KIND_FP_MUL)) {
      functionKind = FunctionDeclarationKind.FP_MUL;
    } else if (kind.equals(BITWUZLA_KIND_FP_NEG)) {
      functionKind = FunctionDeclarationKind.FP_IS_NEGATIVE;
    } else if (kind.equals(BITWUZLA_KIND_FP_REM)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_FP_RTI)) {
      functionKind = FunctionDeclarationKind.FP_ROUND_TO_INTEGRAL;
    } else if (kind.equals(BITWUZLA_KIND_FP_SQRT)) {
      functionKind = FunctionDeclarationKind.FP_SQRT;
    } else if (kind.equals(BITWUZLA_KIND_FP_SUB)) {
      functionKind = FunctionDeclarationKind.FP_SUB;
    } else if (kind.equals(BITWUZLA_KIND_FP_TO_FP_FROM_BV)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_FP_TO_FP_FROM_FP)) {
      functionKind = FunctionDeclarationKind.FP_CASTTO_FP;
    } else if (kind.equals(BITWUZLA_KIND_FP_TO_FP_FROM_SBV)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_FP_TO_FP_FROM_UBV)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else if (kind.equals(BITWUZLA_KIND_FP_TO_SBV)) {
      functionKind = FunctionDeclarationKind.FP_CASTTO_SBV;
    } else if (kind.equals(BITWUZLA_KIND_FP_TO_UBV)) {
      functionKind = FunctionDeclarationKind.FP_CASTTO_UBV;
    } else if (kind.equals(BITWUZLA_KIND_NUM_KINDS)) {
      functionKind = FunctionDeclarationKind.OTHER;
    } else {
      throw new UnsupportedOperationException(
          "Visitor currently does not support visiting " + kind.toString());
    }

    assert (functionKind != null);

    if (functionName == null) {
      functionName = functionKind.toString();
    }
    if (functionArgs.isEmpty()) {
      for (int i = 0; i < numberOfArgs; i++) {
        long pCurrentTerm = bitwuzlaJNI.BitwuzlaTermArray_getitem(pfunctionArgs, i);
        long pCurrentSort = bitwuzlaJNI.bitwuzla_term_get_sort(pCurrentTerm);
        FormulaType<? extends Formula> currentType = bitwuzlaSortToType(pCurrentSort);
        argTypes.add(currentType);
        functionArgs.add(encapsulate(currentType, pCurrentTerm));
      }
    }

    Preconditions.checkState(
        functionArgs.size() == argTypes.size(),
        "different size of args (%s) and their types (%s) in term %s",
        functionArgs,
        argTypes,
        f);

    return visitor.visitFunction(
        formula,
        functionArgs,
        FunctionDeclarationImpl.of(functionName, functionKind, argTypes, getFormulaType(f), kind));
  }

  @Override
  public FormulaType<?> getFormulaType(Long formula) {
    long pType = bitwuzlaJNI.bitwuzla_term_get_sort(formula);
    return bitwuzlaSortToType(pType);
  }

  private BigDecimal parseIEEEbinaryFP(long pTerm) {
    // The Bitwuzla string for FPs is always in binary, regardless of the second argument.

    String fp = bitwuzlaJNI.bitwuzla_term_value_get_str(pTerm, 2);

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
    if (bitwuzlaJNI.bitwuzla_term_is_bv_value(f)) {
      return visitor.visitConstant(
          formula, new BigInteger(bitwuzlaJNI.bitwuzla_term_value_get_str(f, 10)));
    } else if (bitwuzlaJNI.bitwuzla_term_is_fp_value(f)) {
      return visitor.visitConstant(formula, parseIEEEbinaryFP(f));
    } else if (bitwuzlaJNI.bitwuzla_term_is_const(f)) {
      String name = bitwuzlaJNI.bitwuzla_term_get_symbol(f);
      return visitor.visitFreeVariable(formula, name);
    } else if (bitwuzlaJNI.bitwuzla_term_is_var(f)) {
      return visitor.visitBoundVariable(formula, 0);
    } else {
      return visitKind(visitor, formula, f);
    }
  }

  @Override
  public Long callFunctionImpl(Long declaration, List<Long> args) {
    long[] functionAndArgs =
        LongStream.concat(LongStream.of(declaration), args.stream().mapToLong(Long::longValue))
            .toArray();
    return bitwuzlaJNI.bitwuzla_mk_term(
        BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue(), args.size(), functionAndArgs);

    //    return bitwuzlaJNI.bitwuzla_mk_term(declaration.intValue(), args.size(),
    //        args.stream().mapToLong(Long::longValue).toArray());
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
      long pChildren = bitwuzlaJNI.bitwuzla_term_get_children(pLong, size);
      // Returns pointer to Uninterpreted Function used in Apply
      return bitwuzlaJNI.BitwuzlaTermArray_getitem(pChildren, 0);
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
}
