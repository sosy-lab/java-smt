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
package org.sosy_lab.solver.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Function;
import com.google.common.base.Preconditions;
import com.google.common.collect.Collections2;
import com.google.common.collect.Iterables;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.FunctionDeclarationKind;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.solver.visitors.BooleanFormulaVisitor;
import org.sosy_lab.solver.visitors.FormulaVisitor;
import org.sosy_lab.solver.visitors.TraversalProcess;

import java.util.Collection;
import java.util.List;

public abstract class AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv> implements BooleanFormulaManager {

  protected AbstractBooleanFormulaManager(FormulaCreator<TFormulaInfo, TType, TEnv> pCreator) {
    super(pCreator);
  }

  private BooleanFormula wrap(TFormulaInfo formulaInfo) {
    return getFormulaCreator().encapsulateBoolean(formulaInfo);
  }

  @Override
  public BooleanFormula makeVariable(String pVar) {
    return wrap(makeVariableImpl(pVar));
  }

  protected abstract TFormulaInfo makeVariableImpl(String pVar);

  @Override
  public BooleanFormula makeBoolean(boolean value) {
    return wrap(makeBooleanImpl(value));
  }

  protected abstract TFormulaInfo makeBooleanImpl(boolean value);

  @Override
  public BooleanFormula not(BooleanFormula pBits) {
    TFormulaInfo param1 = extractInfo(pBits);
    return wrap(not(param1));
  }

  protected abstract TFormulaInfo not(TFormulaInfo pParam1);

  @Override
  public BooleanFormula and(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);

    return wrap(and(param1, param2));
  }

  protected abstract TFormulaInfo and(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula and(Collection<BooleanFormula> pBits) {
    if (pBits.isEmpty()) {
      return makeBoolean(true);
    }
    if (pBits.size() == 1) {
      return Iterables.getOnlyElement(pBits);
    }
    TFormulaInfo result = andImpl(Collections2.transform(pBits, extractor));
    return wrap(result);
  }

  protected TFormulaInfo andImpl(Collection<TFormulaInfo> pParams) {
    TFormulaInfo result = makeBooleanImpl(true);
    for (TFormulaInfo formula : pParams) {
      result = and(result, formula);
    }
    return result;
  }

  @Override
  public BooleanFormula or(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);

    return wrap(or(param1, param2));
  }

  protected abstract TFormulaInfo or(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula xor(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);

    return wrap(xor(param1, param2));
  }

  @Override
  public BooleanFormula or(Collection<BooleanFormula> pBits) {
    if (pBits.isEmpty()) {
      return makeBoolean(false);
    }
    if (pBits.size() == 1) {
      return Iterables.getOnlyElement(pBits);
    }
    TFormulaInfo result = orImpl(Collections2.transform(pBits, extractor));
    return wrap(result);
  }

  protected TFormulaInfo orImpl(Collection<TFormulaInfo> pParams) {
    TFormulaInfo result = makeBooleanImpl(false);
    for (TFormulaInfo formula : pParams) {
      result = or(result, formula);
    }
    return result;
  }

  protected abstract TFormulaInfo xor(TFormulaInfo pParam1, TFormulaInfo pParam2);

  /**
   * Creates a formula representing an equivalence of the two arguments.
   * @param pBits1 a Formula
   * @param pBits2 a Formula
   * @return {@code f1 <-> f2}
   */
  @Override
  public final BooleanFormula equivalence(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);
    return wrap(equivalence(param1, param2));
  }

  protected abstract TFormulaInfo equivalence(TFormulaInfo bits1, TFormulaInfo bits2);

  @Override
  public final BooleanFormula implication(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);
    return wrap(implication(param1, param2));
  }

  protected TFormulaInfo implication(TFormulaInfo bits1, TFormulaInfo bits2) {
    return or(not(bits1), bits2);
  }

  @Override
  public final boolean isTrue(BooleanFormula pBits) {
    return isTrue(extractInfo(pBits));
  }

  protected abstract boolean isTrue(TFormulaInfo bits);

  @Override
  public final boolean isFalse(BooleanFormula pBits) {
    return isFalse(extractInfo(pBits));
  }

  protected abstract boolean isFalse(TFormulaInfo bits);

  /**
   * Creates a formula representing "IF cond THEN f1 ELSE f2"
   * @param pBits a Formula
   * @param f1 a Formula
   * @param f2 a Formula
   * @return (IF cond THEN f1 ELSE f2)
   */
  @Override
  public final <T extends Formula> T ifThenElse(BooleanFormula pBits, T f1, T f2) {
    FormulaType<T> t1 = getFormulaCreator().getFormulaType(f1);
    FormulaType<T> t2 = getFormulaCreator().getFormulaType(f2);
    checkArgument(
        t1.equals(t2),
        "Cannot create if-then-else formula with branches of different types: "
            + "%s is of type %s; %s is of type %s",
        f1,
        t1,
        f2,
        t2);
    TFormulaInfo result = ifThenElse(extractInfo(pBits), extractInfo(f1), extractInfo(f2));
    return getFormulaCreator().encapsulate(t1, result);
  }

  protected abstract TFormulaInfo ifThenElse(TFormulaInfo cond, TFormulaInfo f1, TFormulaInfo f2);

  @Override
  public <R> R visit(BooleanFormulaVisitor<R> visitor, BooleanFormula pFormula) {
    return formulaCreator.visit(new DelegatingFormulaVisitor<>(visitor), pFormula);
  }

  private class DelegatingFormulaVisitor<R> implements FormulaVisitor<R> {
    private final BooleanFormulaVisitor<R> delegate;

    DelegatingFormulaVisitor(BooleanFormulaVisitor<R> pDelegate) {
      delegate = pDelegate;
    }

    @Override
    public R visitFreeVariable(Formula f, String name) {

      // Only boolean formulas can appear here.
      assert f instanceof BooleanFormula;
      return delegate.visitAtom((BooleanFormula) f, FunctionDeclaration.of(name, FunctionDeclarationKind.VAR));
    }

    @Override
    public R visitBoundVariable(Formula f, int deBruijnIdx) {

      // Only boolean formulas can appear here.
      assert f instanceof BooleanFormula;
      return delegate.visitBoundVar((BooleanFormula) f, deBruijnIdx);
    }

    @Override
    public R visitConstant(Formula f, Object value) {
      Preconditions.checkState(value instanceof Boolean);
      boolean v = (Boolean) value;
      if (v) {
        return delegate.visitTrue();
      } else {
        return delegate.visitFalse();
      }
    }

    private List<BooleanFormula> getBoolArgs(List<Formula> args) {
      @SuppressWarnings("unchecked")
      List<BooleanFormula> out = (List<BooleanFormula>) (List<?>) args;
      return out;
    }

    @Override
    public R visitFunction(
        Formula f,
        List<Formula> args,
        FunctionDeclaration functionDeclaration,
        Function<List<Formula>, Formula> newApplicationConstructor) {
      switch (functionDeclaration.getKind()) {
        case AND:
          Preconditions.checkState(args.iterator().next() instanceof BooleanFormula);
          R out = delegate.visitAnd(getBoolArgs(args));
          return out;
        case NOT:
          Preconditions.checkState(args.size() == 1);
          Formula arg = args.get(0);

          Preconditions.checkArgument(arg instanceof BooleanFormula);
          return delegate.visitNot((BooleanFormula) arg);
        case OR:
          Preconditions.checkState(args.iterator().next() instanceof BooleanFormula);
          R out2 = delegate.visitOr(getBoolArgs(args));
          return out2;
        case IFF:
          Preconditions.checkState(args.size() == 2);
          Formula a = args.get(0);
          Formula b = args.get(1);
          Preconditions.checkState(a instanceof BooleanFormula && b instanceof BooleanFormula);
          R out3 = delegate.visitEquivalence((BooleanFormula) a, (BooleanFormula) b);
          return out3;
        case ITE:
          Preconditions.checkArgument(args.size() == 3);
          Formula ifC = args.get(0);
          Formula then = args.get(1);
          Formula elseC = args.get(2);
          Preconditions.checkState(
              ifC instanceof BooleanFormula
                  && then instanceof BooleanFormula
                  && elseC instanceof BooleanFormula);
          return delegate.visitIfThenElse(
              (BooleanFormula) ifC, (BooleanFormula) then, (BooleanFormula) elseC);
        case XOR:
          Preconditions.checkArgument(args.size() == 2);
          Formula a1 = args.get(0);
          Formula a2 = args.get(1);
          Preconditions.checkState(a1 instanceof BooleanFormula && a2 instanceof BooleanFormula);
          return delegate.visitXor((BooleanFormula) a1, (BooleanFormula) a2);
        case IMPLIES:
          Preconditions.checkArgument(args.size() == 2);
          Formula b1 = args.get(0);
          Formula b2 = args.get(1);
          Preconditions.checkArgument(b1 instanceof BooleanFormula && b2 instanceof BooleanFormula);
          return delegate.visitImplication((BooleanFormula) b1, (BooleanFormula) b2);
        default:
          return delegate.visitAtom((BooleanFormula) f, functionDeclaration);
      }
    }

    @Override
    public R visitQuantifier(
        BooleanFormula f,
        Quantifier quantifier,
        List<Formula> boundVariables,
        BooleanFormula body) {
      return delegate.visitQuantifier(quantifier, boundVariables, body);
    }
  }

  @Override
  public void visitRecursively(
      BooleanFormulaVisitor<TraversalProcess> pFormulaVisitor, BooleanFormula pF) {
    RecursiveBooleanFormulaVisitor recVisitor = new RecursiveBooleanFormulaVisitor(pFormulaVisitor);
    recVisitor.addToQueue(pF);
    while (!recVisitor.isQueueEmpty()) {
      TraversalProcess process = checkNotNull(visit(recVisitor, recVisitor.pop()));
      if (process == TraversalProcess.ABORT) {
        return;
      }
    }
  }
}
