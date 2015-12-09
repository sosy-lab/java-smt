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

import com.google.common.base.Preconditions;
import com.google.common.primitives.Longs;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.solver.visitors.BooleanFormulaVisitor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

class Z3BooleanFormulaManager extends AbstractBooleanFormulaManager<Long, Long, Long> {

  private final long z3context;

  Z3BooleanFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    this.z3context = creator.getEnv();
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

  /**
   * @param pParam Z3_ast
   * @return Z3_ast with the tactic applied.
   */
  @Override
  public Long applyTacticImpl(Long pParam, Tactic tactic) {
    return Z3NativeApiHelpers.applyTactic(z3context, pParam, tactic.getTacticName());
  }

  // copied from Z3UnsafeFormulaManager
  private boolean isAtom(Long t) {
    int astKind = get_ast_kind(z3context, t);
    switch (astKind) {
      case Z3_APP_AST:
        long decl = get_app_decl(z3context, t);
        return !Z3UnsafeFormulaManager.NON_ATOMIC_OP_TYPES.contains(get_decl_kind(z3context, decl));
      case Z3_QUANTIFIER_AST:
        return false;
      default:
        return true;
    }
  }

  // copied from Z3UnsafeFormulaManager
  private int getArity(Long t) {
    Preconditions.checkArgument(get_ast_kind(z3context, t) == Z3_APP_AST);
    return get_app_num_args(z3context, t);
  }

  // copied from Z3UnsafeFormulaManager
  private BooleanFormula getArg(Long pF, int index) {
    assert getFormulaCreator().getBoolType().equals(getFormulaCreator().getFormulaType(pF));
    return getFormulaCreator().encapsulateBoolean(get_app_arg(z3context, pF, index));
  }

  private List<BooleanFormula> getAllArgs(Long pF) {
    int arity = getArity(pF);
    List<BooleanFormula> args = new ArrayList<>(arity);
    for (int i = 0; i < arity; i++) {
      args.add(getArg(pF, i));
    }
    return args;
  }

  @Override
  protected <R> R visit(BooleanFormulaVisitor<R> pVisitor, Long f) {
    if (isTrue(f)) {
      assert getArity(f) == 0;
      return pVisitor.visitTrue();
    }

    if (isFalse(f)) {
      assert getArity(f) == 0;
      return pVisitor.visitFalse();
    }

    if (isNot(f)) {
      assert getArity(f) == 1;
      return pVisitor.visitNot(getArg(f, 0));
    }

    if (isAnd(f)) {
      if (getArity(f) == 0) {
        return pVisitor.visitTrue();
      } else if (getArity(f) == 1) {
        return visit(pVisitor, getArg(f, 0));
      }
      return pVisitor.visitAnd(getAllArgs(f));
    }

    if (isOr(f)) {
      if (getArity(f) == 0) {
        return pVisitor.visitFalse();
      } else if (getArity(f) == 1) {
        return pVisitor.visit(getArg(f, 0));
      }
      return pVisitor.visitOr(getAllArgs(f));
    }

    if (isEquivalence(f)) {
      assert getArity(f) == 2;
      return pVisitor.visitEquivalence(getArg(f, 0), getArg(f, 1));
    }

    if (isIfThenElse(f)) {
      assert getArity(f) == 3;
      return pVisitor.visitIfThenElse(getArg(f, 0), getArg(f, 1), getArg(f, 2));
    }

    if (isAtom(f)) {
      return pVisitor.visitAtom(getFormulaCreator().encapsulateBoolean(f));
    }

    throw new UnsupportedOperationException("Unknown or unsupported boolean operator " + f);
  }
}
