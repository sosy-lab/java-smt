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

import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_AND;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_EQ;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_IFF;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_ITE;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_LEQ;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_NOT;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_OR;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.MSAT_TAG_PLUS;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_decl_get_name;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_decl_get_tag;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_make_term;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_arity;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_get_arg;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_get_decl;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_constant;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_false;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_number;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_true;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_is_uf;
import static org.sosy_lab.solver.mathsat5.Mathsat5NativeApi.msat_term_repr;

import com.google.common.base.Function;
import com.google.common.primitives.Longs;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FuncDecl;
import org.sosy_lab.solver.api.FuncDeclKind;
import org.sosy_lab.solver.basicimpl.AbstractIntrospectionFormulaManager;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import java.util.ArrayList;
import java.util.List;

class Mathsat5IntrospectionFormulaManager
    extends AbstractIntrospectionFormulaManager<Long, Long, Long> {

  private final long msatEnv;
  private final Mathsat5FormulaCreator formulaCreator;

  Mathsat5IntrospectionFormulaManager(Mathsat5FormulaCreator pCreator) {
    super(pCreator);
    this.msatEnv = pCreator.getEnv();
    this.formulaCreator = pCreator;
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, final Long f) {
    int arity = msat_term_arity(f);
    if (msat_term_is_number(msatEnv, f)) {

      // TODO extract logic from Mathsat5Model for conversion from string to number and use it here
      return visitor.visitConstant(formula, msat_term_repr(f));
    } else if (msat_term_is_true(msatEnv, f)) {
      return visitor.visitConstant(formula, true);
    } else if (msat_term_is_false(msatEnv, f)) {
      return visitor.visitConstant(formula, false);
    } else if (msat_term_is_constant(msatEnv, f)) {
      return visitor.visitFreeVariable(formula, msat_term_repr(f));
    } else {

      List<Formula> args = new ArrayList<>(arity);
      for (int i = 0; i < arity; i++) {
        long arg = msat_term_get_arg(f, i);
        FormulaType<?> argumentType = formulaCreator.getFormulaType(arg);
        args.add(formulaCreator.encapsulate(argumentType, arg));
      }

      String name = getName(f);

      // Any function application.
      Function<List<Formula>, Formula> constructor =
          new Function<List<Formula>, Formula>() {
            @Override
            public Formula apply(List<Formula> formulas) {
              return formulaCreator.encapsulateWithTypeOf(replaceArgs(f, extractInfo(formulas)));
            }
          };
      return visitor.visitFuncApp(
          formula, args, FuncDecl.of(name, getDeclarationKind(f)), constructor);
    }
  }

  private String getName(Long t) {
    if (msat_term_is_constant(msatEnv, t)) {
      return msat_term_repr(t);
    } else {
      return msat_decl_get_name(msat_term_get_decl(t));
    }
  }

  private Long replaceArgs(Long t, List<Long> newArgs) {
    long tDecl = msat_term_get_decl(t);
    return msat_make_term(msatEnv, tDecl, Longs.toArray(newArgs));
  }

  private FuncDeclKind getDeclarationKind(long pF) {
    if (msat_term_is_uf(msatEnv, pF)) {
      return FuncDeclKind.UF;
    } else if (msat_term_is_constant(msatEnv, pF)) {
      return FuncDeclKind.VAR;
    }

    long decl = msat_term_get_decl(pF);
    int tag = msat_decl_get_tag(msatEnv, decl);
    switch (tag) {
      case MSAT_TAG_AND:
        return FuncDeclKind.AND;
      case MSAT_TAG_NOT:
        return FuncDeclKind.NOT;
      case MSAT_TAG_OR:
        return FuncDeclKind.OR;
      case MSAT_TAG_IFF:
        return FuncDeclKind.IFF;
      case MSAT_TAG_ITE:
        return FuncDeclKind.ITE;

      case MSAT_TAG_PLUS:
        return FuncDeclKind.ADD;
      case MSAT_TAG_LEQ:
        return FuncDeclKind.LTE;
      case MSAT_TAG_EQ:
        return FuncDeclKind.EQ;
      default:
        return FuncDeclKind.OTHER;
    }
  }
}
