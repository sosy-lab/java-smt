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
package org.sosy_lab.solver.z3java;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.solver.z3java.Z3NativeApi.ast_to_string;
import static org.sosy_lab.solver.z3java.Z3NativeApi.dec_ref;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_app_arg;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_app_decl;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_app_num_args;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_arity;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_array_sort_domain;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_array_sort_range;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_ast_kind;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_bv_sort_size;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_decl_kind;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_decl_name;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_index_value;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_numeral_string;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_quantifier_body;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_quantifier_bound_name;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_quantifier_bound_sort;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_quantifier_num_bound;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_sort;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_sort_kind;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_symbol_int;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_symbol_kind;
import static org.sosy_lab.solver.z3java.Z3NativeApi.get_symbol_string;
import static org.sosy_lab.solver.z3java.Z3NativeApi.inc_ref;
import static org.sosy_lab.solver.z3java.Z3NativeApi.is_quantifier_forall;
import static org.sosy_lab.solver.z3java.Z3NativeApi.mk_const;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_APP_AST;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_ARRAY_SORT;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_BOOL_SORT;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_BV_SORT;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_FUNC_DECL_AST;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_INT_SORT;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_INT_SYMBOL;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_NUMERAL_AST;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_ADD;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_AND;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_DISTINCT;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_DIV;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_EQ;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_FALSE;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_GE;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_GT;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_IFF;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_ITE;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_LE;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_LT;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_MOD;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_MUL;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_NOT;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_OR;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_SUB;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_TRUE;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_UNINTERPRETED;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_OP_XOR;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_QUANTIFIER_AST;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_REAL_SORT;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_SORT_AST;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_STRING_SYMBOL;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_UNKNOWN_AST;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.Z3_VAR_AST;
import static org.sosy_lab.solver.z3java.Z3NativeApiConstants.isOP;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Maps;
import com.google.common.collect.Table;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import com.microsoft.z3.StringSymbol;
import com.microsoft.z3.enumerations.Z3_sort_kind;

import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.common.time.Timer;
import org.sosy_lab.solver.api.ArrayFormula;
import org.sosy_lab.solver.api.BitvectorFormula;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.FunctionDeclarationKind;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.solver.basicimpl.FormulaCreator;
import org.sosy_lab.solver.visitors.FormulaVisitor;
import org.sosy_lab.solver.z3java.Z3Formula.Z3ArrayFormula;

import java.lang.ref.PhantomReference;
import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

@Options(prefix = "solver.z3")
class Z3FormulaCreator extends FormulaCreator<Expr, Sort, Context> {

  @Option(secure = true, description = "Whether to use PhantomReferences for discarding Z3 AST")
  private boolean usePhantomReferences = false;

  private final Table<Sort, Sort, Sort> allocatedArraySorts = HashBasedTable.create();

  private final ReferenceQueue<Z3Formula> referenceQueue = new ReferenceQueue<>();
  private final Map<PhantomReference<? extends Z3Formula>, Long> referenceMap =
      Maps.newIdentityHashMap();

  // todo: getters for statistic.
  private final Timer cleanupTimer = new Timer();

  Z3FormulaCreator(
      Context pEnv, Sort pBoolType, Sort pIntegerType, Sort pRealType, Configuration config)
      throws InvalidConfigurationException {
    super(pEnv, pBoolType, pIntegerType, pRealType);
    config.inject(this);
  }

  @Override
  public Expr makeVariable(Sort type, String varName) {
    Context z3context = getEnv();
    StringSymbol symbol = z3context.mkSymbol(varName);
    return z3context.mkConst(symbol, type);
  }

  @Override
  public Expr extractInfo(Formula pT) {
    return Z3FormulaManager.getZ3Expr(pT);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    if (pFormula instanceof ArrayFormula<?, ?> || pFormula instanceof BitvectorFormula) {
      Expr term = extractInfo(pFormula);
      return (FormulaType<T>) getFormulaType(term);
    }

    return super.getFormulaType(pFormula);
  }

  public FormulaType<?> getFormulaTypeFromSort(Sort pSort) {
    Context z3context = getEnv();
    Z3_sort_kind sortKind = pSort.getSortKind();
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
    }
    throw new IllegalArgumentException("Unknown formula type");
  }

  @Override
  public FormulaType<?> getFormulaType(Expr pFormula) {
    return getFormulaTypeFromSort(pFormula.getSort());
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

  private <T extends Z3Formula> T storePhantomReference(T out, Long pTerm) {
    if (usePhantomReferences) {
      PhantomReference<T> ref = new PhantomReference<>(out, referenceQueue);
      referenceMap.put(ref, pTerm);
    }
    return out;
  }

  @Override
  public Sort getArrayType(Sort pIndexType, Sort pElementType) {
    Sort allocatedArraySort = allocatedArraySorts.get(pIndexType, pElementType);
    if (allocatedArraySort == null) {
      allocatedArraySort = getEnv().mkArraySort(pIndexType, pElementType);
      allocatedArraySorts.put(pIndexType, pElementType, allocatedArraySort);
    }
    return allocatedArraySort;
  }

  @Override
  public Sort getBitvectorType(int pBitwidth) {
    checkArgument(pBitwidth > 0, "Cannot use bitvector type with size %s", pBitwidth);
    return getEnv().mkBitVecSort(pBitwidth);
  }

  @Override
  public Sort getFloatingPointType(FormulaType.FloatingPointType type) {
    throw new UnsupportedOperationException("FloatingPoint theory is not supported by Z3");
  }

  private void cleanupReferences() {
    if (!usePhantomReferences) {
      return;
    }
    cleanupTimer.start();
    try {
      Reference<? extends Z3Formula> ref;
      while ((ref = referenceQueue.poll()) != null) {

        Long z3ast = referenceMap.remove(ref);
        assert z3ast != null;
        dec_ref(getEnv(), z3ast);
      }
    } finally {
      cleanupTimer.stop();
    }
  }

  private String getName(Long t) {
    int astKind = get_ast_kind(environment, t);
    if (astKind == Z3_VAR_AST) {
      return "?" + get_index_value(environment, t);
    } else {
      long funcDecl = get_app_decl(environment, t);
      long symbol = get_decl_name(environment, funcDecl);
      switch (get_symbol_kind(environment, symbol)) {
        case Z3_INT_SYMBOL:
          return Integer.toString(get_symbol_int(environment, symbol));
        case Z3_STRING_SYMBOL:
          return get_symbol_string(environment, symbol);
        default:
          throw new AssertionError();
      }
    }
  }

  private Expr replaceArgs(Expr t, List<Expr> newArgs) {
    Preconditions.checkState(t.getNumArgs() == newArgs.size());
    Expr[] newParams = newArgs.toArray(new Expr[]{});
    // TODO check equality of sort of each oldArg and newArg
    return environment.mkApp(t.getFuncDecl(), newParams);
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, final Formula formula, final Long f) {
    switch (get_ast_kind(environment, f)) {
      case Z3_NUMERAL_AST:
        return visitor.visitConstant(formula, convertValue(f));
      case Z3_APP_AST:
        String name = getName(f);
        int arity = get_app_num_args(environment, f);

        if (arity == 0) {

          // true/false.
          long declKind = get_decl_kind(environment, get_app_decl(environment, f));
          if (declKind == Z3_OP_TRUE || declKind == Z3_OP_FALSE) {
            return visitor.visitConstant(formula, declKind == Z3_OP_TRUE);
          } else {

            // Has to be a variable otherwise.
            // TODO: assert that.
            return visitor.visitFreeVariable(formula, name);
          }
        }

        List<Formula> args = new ArrayList<>(arity);
        for (int i = 0; i < arity; i++) {
          long arg = get_app_arg(environment, f, i);
          FormulaType<?> argumentType = getFormulaType(arg);
          args.add(encapsulate(argumentType, arg));
        }

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

    if (get_arity(environment, f) == 0) {
      return FunctionDeclarationKind.VAR;
    }

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

      default:
        return FunctionDeclarationKind.OTHER;
    }
  }

  public Object convertValue(Long value) {
    inc_ref(environment, value);
    try {
      FormulaType<?> type = getFormulaType(value);
      Object lValue;
      if (type.isBooleanType()) {
        return isOP(environment, value, Z3_OP_TRUE);
      } else if (type.isIntegerType()) {
        return new BigInteger(get_numeral_string(environment, value));
      } else if (type.isRationalType()) {

        // String serialization is expensive, but getting arbitrary-sized
        // numbers is difficult otherwise.
        // TODO: an optimization is possible here, try to get an integer first,
        // resort to strings if that fails.
        String s = get_numeral_string(environment, value);
        return Rational.ofString(s);
      } else if (type.isBitvectorType()) {
        return interpretBitvector(environment, value);
      } else {

        // Unknown type --- return string serialization.
        return ast_to_string(environment, value);
      }

    } finally {
      dec_ref(environment, value);
    }
  }

  private static BigInteger interpretBitvector(long z3context, long bv) {
    long argSort = get_sort(z3context, bv);
    int sortKind = get_sort_kind(z3context, argSort);
    Preconditions.checkArgument(sortKind == Z3_BV_SORT);
    return new BigInteger(get_numeral_string(z3context, bv));
  }
}
