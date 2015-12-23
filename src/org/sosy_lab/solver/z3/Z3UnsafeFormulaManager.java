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
import static org.sosy_lab.solver.z3.Z3NativeApi.func_decl_to_ast;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_arg;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_decl;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_num_args;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_ast_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_decl_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_decl_name;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_index_value;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_quantifier_body;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_quantifier_bound_name;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_quantifier_bound_sort;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_quantifier_num_bound;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_quantifier_pattern_ast;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_sort;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_sort_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_symbol_int;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_symbol_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_symbol_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.inc_ref;
import static org.sosy_lab.solver.z3.Z3NativeApi.is_app;
import static org.sosy_lab.solver.z3.Z3NativeApi.is_numeral_ast;
import static org.sosy_lab.solver.z3.Z3NativeApi.is_quantifier_forall;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_app;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_bvuge;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_bvule;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_const;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_func_decl;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_ge;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_le;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_string_symbol;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_APP_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_BV_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_FUNC_DECL_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_INT_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_INT_SYMBOL;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_NUMERAL_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_AND;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_EQ;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_FALSE;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_IMPLIES;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_ITE;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_NOT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_OR;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_TRUE;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_UNINTERPRETED;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_QUANTIFIER_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_REAL_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_SORT_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_STRING_SYMBOL;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_UNKNOWN_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_VAR_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.isOP;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.primitives.Longs;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.basicimpl.AbstractUnsafeFormulaManager;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

class Z3UnsafeFormulaManager extends AbstractUnsafeFormulaManager<Long, Long, Long> {

  private final long z3context;
  private final Z3FormulaCreator formulaCreator;

  Z3UnsafeFormulaManager(Z3FormulaCreator pCreator) {
    super(pCreator);
    this.z3context = pCreator.getEnv();
    formulaCreator = pCreator;
  }

  final static ImmutableSet<Integer> NON_ATOMIC_OP_TYPES =
      ImmutableSet.of(Z3_OP_AND, Z3_OP_OR, Z3_OP_IMPLIES, Z3_OP_ITE, Z3_OP_NOT);

  @Override
  public boolean isAtom(Long t) {
    int astKind = get_ast_kind(z3context, t);
    switch (astKind) {
      case Z3_APP_AST:
        long decl = get_app_decl(z3context, t);
        return !NON_ATOMIC_OP_TYPES.contains(get_decl_kind(z3context, decl));
      case Z3_QUANTIFIER_AST:
        return false;
      default:
        return true;
    }
  }

  @Override
  public int getArity(Long t) {
    Preconditions.checkArgument(get_ast_kind(z3context, t) != Z3_QUANTIFIER_AST);
    return get_app_num_args(z3context, t);
  }

  @Override
  public Long getArg(Long t, int n) {
    Preconditions.checkArgument(get_ast_kind(z3context, t) == Z3_APP_AST);
    return get_app_arg(z3context, t, n);
  }

  @Override
  public boolean isVariable(Long t) {
    if (isOP(z3context, t, Z3_OP_TRUE) || isOP(z3context, t, Z3_OP_FALSE)) {
      return false;
    }
    int astKind = get_ast_kind(z3context, t);
    return (astKind == Z3_VAR_AST) || ((astKind == Z3_APP_AST) && (getArity(t) == 0));
  }

  private boolean isFunctionApplication(long t) {
    return get_ast_kind(z3context, t) == Z3_APP_AST;
  }

  @Override
  protected boolean isFreeVariable(Long pT) {
    if (isOP(z3context, pT, Z3_OP_TRUE) || isOP(z3context, pT, Z3_OP_FALSE)) {
      return false;
    }

    int astKind = get_ast_kind(z3context, pT);
    return ((astKind == Z3_APP_AST) && (getArity(pT) == 0));
  }

  @Override
  protected boolean isBoundVariable(Long pT) {
    int astKind = get_ast_kind(z3context, pT);
    return (astKind == Z3_VAR_AST);
  }

  @Override
  public boolean isUF(Long t) {
    return is_app(z3context, t)
        && get_decl_kind(z3context, get_app_decl(z3context, t)) == Z3_OP_UNINTERPRETED;
  }

  @Override
  public String getName(Long t) {
    int astKind = get_ast_kind(z3context, t);
    if (astKind == Z3_VAR_AST) {
      return "?" + get_index_value(z3context, t);
    } else {
      long funcDecl = get_app_decl(z3context, t);
      long symbol = get_decl_name(z3context, funcDecl);
      switch (get_symbol_kind(z3context, symbol)) {
        case Z3_INT_SYMBOL:
          return Integer.toString(get_symbol_int(z3context, symbol));
        case Z3_STRING_SYMBOL:
          return get_symbol_string(z3context, symbol);
        default:
          throw new AssertionError();
      }
    }
  }

  @Override
  public Long replaceArgs(Long t, List<Long> newArgs) {
    Preconditions.checkState(get_app_num_args(z3context, t) == newArgs.size());
    long[] newParams = Longs.toArray(newArgs);
    // TODO check equality of sort of each oldArg and newArg
    long funcDecl = get_app_decl(z3context, t);
    return mk_app(z3context, funcDecl, newParams);
  }

  @Override
  public Long replaceArgsAndName(Long t, String pNewName, List<Long> newArgs) {
    if (isVariable(t)) {
      checkArgument(newArgs.isEmpty());
      long sort = get_sort(z3context, t);
      return getFormulaCreator().makeVariable(sort, pNewName);

    } else if (isFunctionApplication(t)) {
      int n = get_app_num_args(z3context, t);
      long[] sorts = new long[n];

      for (int i = 0; i < sorts.length; i++) {
        long arg = get_app_arg(z3context, t, i);
        inc_ref(z3context, arg);
        sorts[i] = get_sort(z3context, arg);
        inc_ref(z3context, sorts[i]);
        dec_ref(z3context, arg);
      }
      long symbol = mk_string_symbol(z3context, pNewName);
      long retSort = get_sort(z3context, t);
      long newFunc = mk_func_decl(z3context, symbol, sorts, retSort);
      inc_ref(z3context, func_decl_to_ast(z3context, newFunc));

      long out = mk_app(z3context, newFunc, Longs.toArray(newArgs));

      for (long sort : sorts) {
        dec_ref(z3context, sort);
      }
      dec_ref(z3context, func_decl_to_ast(z3context, newFunc));
      return out;

    } else {
      throw new IllegalArgumentException(
          "Cannot replace name '" + pNewName + "' in term '" + ast_to_string(z3context, t) + "'.");
    }
  }

  @Override
  protected List<Long> splitNumeralEqualityIfPossible(Long pF) {
    if (isOP(z3context, pF, Z3_OP_EQ) && get_app_num_args(z3context, pF) == 2) {
      long arg0 = getArg(pF, 0);
      inc_ref(z3context, arg0);
      long arg1 = getArg(pF, 1);
      inc_ref(z3context, arg1);

      try {
        long sortKind = get_sort_kind(z3context, get_sort(z3context, arg0));
        assert sortKind == get_sort_kind(z3context, get_sort(z3context, arg1));
        if (sortKind == Z3_BV_SORT) {

          long out1 = mk_bvule(z3context, arg0, arg1);
          inc_ref(z3context, out1);
          long out2 = mk_bvuge(z3context, arg0, arg1);
          inc_ref(z3context, out2);

          return ImmutableList.of(out1, out2);
        } else if (sortKind == Z3_INT_SORT || sortKind == Z3_REAL_SORT) {

          long out1 = mk_le(z3context, arg0, arg1);
          inc_ref(z3context, out1);
          long out2 = mk_ge(z3context, arg0, arg1);
          inc_ref(z3context, out2);
          return ImmutableList.of(out1, out2);
        }
      } finally {
        dec_ref(z3context, arg0);
        dec_ref(z3context, arg1);
      }
    }
    return ImmutableList.of(pF);
  }

  @Override
  public boolean isNumber(Long t) {
    return is_numeral_ast(z3context, t);
  }

  @Override
  public Formula substitute(Formula pF, Map<Formula, Formula> pFromToMapping) {
    return substituteUsingLists(pF, pFromToMapping);
  }

  @Override
  protected Long substituteUsingListsImpl(Long t, List<Long> changeFrom, List<Long> changeTo) {
    int size = changeFrom.size();
    Preconditions.checkState(size == changeTo.size());
    return Z3NativeApi.substitute(
        z3context, t, size, Longs.toArray(changeFrom), Longs.toArray(changeTo));
  }

  @Override
  protected boolean isQuantification(Long pT) {
    return Z3_QUANTIFIER_AST == get_ast_kind(z3context, pT);
  }

  @Override
  protected Long getQuantifiedBody(Long pT) {
    return get_quantifier_body(z3context, pT);
  }

  @Override
  protected Long replaceQuantifiedBody(Long pF, Long pBody) {
    boolean isForall = is_quantifier_forall(z3context, pF);
    final int boundCount = get_quantifier_num_bound(z3context, pF);
    long[] boundVars = new long[boundCount];

    for (int b = 0; b < boundCount; b++) {
      long varName = get_quantifier_bound_name(z3context, pF, b);
      long varSort = get_quantifier_bound_sort(z3context, pF, b);
      long var = mk_const(z3context, varName, varSort);
      boundVars[b] = var;
      inc_ref(z3context, var);
    }

    if (isForall) {
      return Z3NativeApi.mk_forall_const(
          z3context, 0, boundCount, boundVars, 0, new long[0], pBody);
    } else {
      return Z3NativeApi.mk_exists_const(
          z3context, 0, boundCount, boundVars, 0, new long[0], pBody);
    }
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, final Long f) {
    String name = getName(f);
    switch (get_ast_kind(z3context, f)) {
      case Z3_NUMERAL_AST:
        // TODO extract logic from Z3Model for conversion from string to number and use it here
        return visitor.visitConstant(ast_to_string(z3context, f), formulaCreator.getFormulaType(f));
      case Z3_APP_AST:
        final FormulaType<?> type = formulaCreator.getFormulaType(f);
        int arity = getArity(f);

        if (arity == 0) {

          // Variable.
          return visitor.visitFreeVariable(name, type);
        }

        List<Formula> args = new ArrayList<>(arity);
        List<FormulaType<?>> formulaTypes = new ArrayList<>(arity);
        for (int i = 0; i < arity; i++) {
          long arg = getArg(f, i);
          FormulaType<?> argumentType = formulaCreator.getFormulaType(arg);
          formulaTypes.add(argumentType);
          args.add(formulaCreator.encapsulate(argumentType, arg));
        }

        if (isUF(f)) {
          // Special casing for UFs.
          return visitor.visitUF(
              name,
              formulaCreator.createUfDeclaration(type, get_app_decl(z3context, f), formulaTypes),
              args);
        } else {
          // Any function application.
          Function<List<Formula>, Formula> constructor =
              new Function<List<Formula>, Formula>() {
                @Override
                public Formula apply(List<Formula> formulas) {
                  return replaceArgs(formulaCreator.encapsulate(type, f), formulas);
                }
              };
          return visitor.visitOperator(name, args, type, constructor);
        }
      case Z3_VAR_AST:
        return visitor.visitBoundVariable(name, formulaCreator.getFormulaType(f));
      case Z3_QUANTIFIER_AST:
        BooleanFormula body = formulaCreator.encapsulateBoolean(get_quantifier_body(z3context, f));
        List<Formula> qargs = new ArrayList<>();
        for (int i = 0; i < get_quantifier_num_bound(z3context, f); i++) {
          long arg = get_quantifier_pattern_ast(z3context, f, i);
          FormulaType<?> argumentType = formulaCreator.getFormulaType(arg);
          qargs.add(formulaCreator.encapsulate(argumentType, arg));
        }

        if (is_quantifier_forall(z3context, f)) {
          return visitor.visitForAll(qargs, body);
        } else {
          return visitor.visitExists(qargs, body);
        }

      case Z3_SORT_AST:
      case Z3_FUNC_DECL_AST:
      case Z3_UNKNOWN_AST:
      default:
        throw new UnsupportedOperationException(
            "Input should be a formula AST, " + "got unexpected type instead");
    }
  }
}
