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

import static org.sosy_lab.solver.z3.Z3NativeApi.ast_to_string;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_arg;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_decl;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_num_args;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_ast_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_decl_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_sort;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_and;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_eq;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_false;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_implies;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_ite;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_not;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_or;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_true;
import static org.sosy_lab.solver.z3.Z3NativeApi.mk_xor;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_APP_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_BOOL_SORT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_AND;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_EQ;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_FALSE;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_IFF;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_IMPLIES;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_ITE;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_NOT;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_OR;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_TRUE;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_OP_XOR;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.Z3_QUANTIFIER_AST;
import static org.sosy_lab.solver.z3.Z3NativeApiConstants.isOP;

import com.google.common.primitives.Longs;

import org.sosy_lab.solver.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.solver.visitors.BooleanFormulaVisitor;

import java.util.Collection;

class Z3BooleanFormulaManager extends AbstractBooleanFormulaManager<Long, Long, Long> {

  private final long z3context;
  private final Z3UnsafeFormulaManager ufmgr;
  private final Z3FormulaCreator creator;

  Z3BooleanFormulaManager(Z3FormulaCreator creator, Z3UnsafeFormulaManager ufmgr) {
    super(creator, ufmgr);
    z3context = creator.getEnv();
    this.creator = creator;
    this.ufmgr = ufmgr;
  }

  @Override
  protected Long makeVariableImpl(String varName) {
    long type = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Long makeBooleanImpl(boolean pValue) {
    if (pValue) {
      return mk_true(z3context);
    } else {
      return mk_false(z3context);
    }
  }

  @Override
  protected Long not(Long pParam) {
    return mk_not(z3context, pParam);
  }

  @Override
  protected Long and(Long pParam1, Long pParam2) {
    return mk_and(z3context, pParam1, pParam2);
  }

  @Override
  protected Long or(Long pParam1, Long pParam2) {
    return mk_or(z3context, pParam1, pParam2);
  }

  @Override
  protected Long orImpl(Collection<Long> params) {
    return mk_or(z3context, params.size(), Longs.toArray(params));
  }

  @Override
  protected Long andImpl(Collection<Long> params) {
    return mk_and(z3context, params.size(), Longs.toArray(params));
  }

  @Override
  protected Long xor(Long pParam1, Long pParam2) {
    return mk_xor(z3context, pParam1, pParam2);
  }

  @Override
  protected boolean isNot(Long pParam) {
    return isOP(z3context, pParam, Z3_OP_NOT);
  }

  @Override
  protected boolean isAnd(Long pParam) {
    return isOP(z3context, pParam, Z3_OP_AND);
  }

  @Override
  protected boolean isOr(Long pParam) {
    return isOP(z3context, pParam, Z3_OP_OR);
  }

  @Override
  protected boolean isXor(Long pParam) {
    return isOP(z3context, pParam, Z3_OP_XOR);
  }

  @Override
  protected Long equivalence(Long pBits1, Long pBits2) {
    return mk_eq(z3context, pBits1, pBits2);
  }

  @Override
  protected Long implication(Long pBits1, Long pBits2) {
    return mk_implies(z3context, pBits1, pBits2);
  }

  @Override
  protected boolean isTrue(Long pParam) {
    return isOP(z3context, pParam, Z3_OP_TRUE);
  }

  @Override
  protected boolean isFalse(Long pParam) {
    return isOP(z3context, pParam, Z3_OP_FALSE);
  }

  @Override
  protected Long ifThenElse(Long pCond, Long pF1, Long pF2) {
    return mk_ite(z3context, pCond, pF1, pF2);
  }

  @Override
  protected boolean isEquivalence(Long pParam) {
    return isOP(z3context, pParam, Z3_OP_IFF)
        || isOP(z3context, pParam, Z3_OP_EQ)
            && get_app_num_args(z3context, pParam) == 2
            && get_sort(z3context, get_app_arg(z3context, pParam, 0)) == Z3_BOOL_SORT
            && get_sort(z3context, get_app_arg(z3context, pParam, 1)) == Z3_BOOL_SORT;
  }

  @Override
  protected boolean isImplication(Long pParam) {
    return isOP(z3context, pParam, Z3_OP_IMPLIES);
  }

  @Override
  protected boolean isIfThenElse(Long pParam) {
    return isOP(z3context, pParam, Z3_OP_ITE);
  }

  @Override
  protected <R> R visit(BooleanFormulaVisitor<R> pVisitor, Long f) {
    switch (get_ast_kind(z3context, f)) {
      case Z3_APP_AST:
        return visitAppAst(pVisitor, f);

      case Z3_QUANTIFIER_AST:

        // todo: duplication of code with FormulaVisitor.
        throw new UnsupportedOperationException("needs to be implemented");

      default:
        throw new UnsupportedOperationException(
            "Unknown or unsupported boolean operator " + ast_to_string(z3context, f));
    }
  }

  private <R> R visitAppAst(BooleanFormulaVisitor<R> pVisitor, Long f)
      throws UnsupportedOperationException {
    final int arity = get_app_num_args(z3context, f);

    switch (get_decl_kind(z3context, get_app_decl(z3context, f))) {
      case Z3_OP_TRUE:
        assert arity == 0;
        return pVisitor.visitTrue();

      case Z3_OP_FALSE:
        assert arity == 0;
        return pVisitor.visitFalse();

      case Z3_OP_NOT:
        assert arity == 1;
        return pVisitor.visitNot(getArg(f, 0));

      case Z3_OP_AND:
        if (arity == 0) {
          return pVisitor.visitTrue();
        } else if (arity == 1) {
          return visit(pVisitor, getArg(f, 0));
        }
        return pVisitor.visitAnd(getAllArgs(f));

      case Z3_OP_OR:
        if (arity == 0) {
          return pVisitor.visitFalse();
        } else if (arity == 1) {
          return visit(pVisitor, getArg(f, 0));
        }
        return pVisitor.visitOr(getAllArgs(f));

      case Z3_OP_IMPLIES:
        assert arity == 2;
        return pVisitor.visitImplication(getArg(f, 0), getArg(f, 1));

      case Z3_OP_ITE:
        assert arity == 3;
        return pVisitor.visitIfThenElse(getArg(f, 0), getArg(f, 1), getArg(f, 2));

      case Z3_OP_IFF:
      case Z3_OP_EQ:
        if (get_app_num_args(z3context, f) == 2
            && get_sort(z3context, get_app_arg(z3context, f, 0)) == Z3_BOOL_SORT
            && get_sort(z3context, get_app_arg(z3context, f, 1)) == Z3_BOOL_SORT) {
          assert arity == 2;
          return pVisitor.visitEquivalence(getArg(f, 0), getArg(f, 1));
        }
        return pVisitor.visitAtom(getFormulaCreator().encapsulateBoolean(f));

      default:
        return pVisitor.visitAtom(getFormulaCreator().encapsulateBoolean(f));
    }
  }
}
