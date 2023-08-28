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

import com.google.common.collect.Table;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BitwuzlaFormulaCreator extends FormulaCreator<Long, Long, Long, Long> {
  protected BitwuzlaFormulaCreator(Long pBitwuzlaEnv) {
    super(pBitwuzlaEnv, bitwuzlaJNI.bitwuzla_mk_bool_sort(), null, null, null, null);
  }

  @Override
  public Long getBitvectorType(int bitwidth) {
    return bitwuzlaJNI.bitwuzla_mk_bv_sort( bitwidth);
  }

  // Assuming that JavaSMT FloatingPointType follows IEEE 754, if it is in the decimal
  // system instead use bitwuzla_mk_fp_value_from_real somehow or convert myself
  @Override
  public Long getFloatingPointType(FloatingPointType type) {
    long fpSort =
        bitwuzlaJNI.bitwuzla_mk_fp_sort( type.getExponentSize(), type.getMantissaSize());
    return fpSort;
  }

  @Override
  public Long getArrayType(Long indexType, Long elementType) {
    return bitwuzlaJNI.bitwuzla_mk_array_sort( indexType, elementType);
  }

  @Override
  public Long makeVariable(Long pLong, String varName) {
    return bitwuzlaJNI.bitwuzla_mk_const( pLong, varName);
  }

  // TODO What about function types? BW has function Sorts. bitwuzla_sort_is_uninterpreted() in
  //  doc, but not in bitwuzla.h for the C API?
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
    } else {
      throw new UnsupportedOperationException("Unsupported Formulatype.");
    }
  }

  @Override
  public FormulaType<?> getFormulaType(Long formula) {
    long pType = bitwuzlaJNI.bitwuzla_term_get_sort(formula);
    return bitwuzlaSortToType(pType);
  }

  /**
   * @param visitor
   * @param formula
   * @param f
   * @see FormulaManager#visit
   */

  // TODO: No easy way to get the abstract constructor, only the very granular FormulaKind. Maybe
  // create hashmaps for each type of kind, and then check in which hashmap the kind is?
  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, Long f) {

    if (bitwuzlaJNI.bitwuzla_term_is_const(f)){
      visitor.visitConstant(f, bitwuzlaJNI.bitwuzla_get_value());
      if(bitwuzlaJNI.bitwuzla_term_is_bool(f)){
        String value = bitwuzlaJNI.bitwuzla_get_value()
        visitor.visitConstant(f, new BigInteger(value))
      }
    } else if (bitwuzlaJNI.bitwuzla_term_is_var(f)) {
      bj.var
      visitor.visitBoundVariable(f, )
    } else if (bitwuzlaJNI.bitwuzla_term_is_fun(f)) {
      visitor.visitFunction()
    } else {
      BitwuzlaKind kind = BitwuzlaKind.swigToEnum(bitwuzlaJNI.bitwuzla_term_get_kind(f));
      if (kind == BitwuzlaKind.BITWUZLA_KIND_EXISTS || kind == BitwuzlaKind.BITWUZLA_KIND_FORALL){
        Quantifier forall = Quantifier.FORALL;
        visitor.visitQuantifier(f)
      }
      String name = kind.toString();
    }
    return null;
  }

  @Override
  public Long callFunctionImpl(Long declaration, List<Long> args) {
//    long[] functionAndArgs =
//        LongStream.concat(LongStream.of(declaration), args.stream().mapToLong(Long::longValue))
//            .toArray();
//    return bitwuzlaJNI.bitwuzla_mk_term(
//        SWIG_BitwuzlaKind.BITWUZLA_KIND_APPLY.swigValue(), args.size(), functionAndArgs);

    return bitwuzlaJNI.bitwuzla_mk_term(declaration.intValue(), args.size(),
        args.stream().mapToLong(Long::longValue).toArray());
  }

  @Override
  public Long declareUFImpl(String pName, Long pReturnType, List<Long> pArgTypes) {
    long functionSort = bitwuzlaJNI.bitwuzla_mk_fun_sort(pArgTypes.size(),
        pArgTypes.stream().mapToLong(Long::longValue).toArray(), pReturnType);
    return bitwuzlaJNI.bitwuzla_mk_const(functionSort, pName);
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(Long pLong) {
    long boolSort = bitwuzlaJNI.bitwuzla_mk_bool_sort();
    return
  }

  public Table<String, Long, Long> getCache() {
    return null;
  }
}