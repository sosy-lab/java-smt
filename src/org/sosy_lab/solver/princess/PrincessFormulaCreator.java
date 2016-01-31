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
package org.sosy_lab.solver.princess;

import static ap.basetypes.IdealInt.ONE;
import static ap.basetypes.IdealInt.ZERO;
import static com.google.common.base.Preconditions.checkArgument;

import ap.basetypes.IdealInt;
import ap.parser.IBoolLit;
import ap.parser.IExpression;
import ap.parser.IExpression.BooleanFunApplier;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IFunction;
import ap.parser.IIntLit;
import ap.parser.ITerm;
import ap.parser.ITermITE;

import com.google.common.base.Function;

import org.sosy_lab.solver.api.ArrayFormula;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.FunctionDeclarationKind;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.solver.basicimpl.FormulaCreator;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import scala.collection.mutable.ArrayBuffer;

import java.util.ArrayList;
import java.util.List;

class PrincessFormulaCreator
    extends FormulaCreator<IExpression, PrincessTermType, PrincessEnvironment> {

  PrincessFormulaCreator(
      PrincessEnvironment pEnv, PrincessTermType pBoolType, PrincessTermType pIntegerType) {
    super(pEnv, pBoolType, pIntegerType, null);
  }

  @Override
  public FormulaType<?> getFormulaType(IExpression pFormula) {
    if (getEnv().hasArrayType(pFormula)) {
      return new ArrayFormulaType<>(FormulaType.IntegerType, FormulaType.IntegerType);
    } else if (PrincessUtil.isBoolean(pFormula)) {
      return FormulaType.BooleanType;
    } else if (PrincessUtil.hasIntegerType(pFormula)) {
      return FormulaType.IntegerType;
    }
    throw new IllegalArgumentException("Unknown formula type");
  }

  @Override
  public IExpression makeVariable(PrincessTermType type, String varName) {
    return getEnv().makeVariable(type, varName);
  }

  @Override
  public PrincessTermType getBitvectorType(int pBitwidth) {
    throw new UnsupportedOperationException("Bitvector theory is not supported by Princess");
  }

  @Override
  public PrincessTermType getFloatingPointType(FormulaType.FloatingPointType type) {
    throw new UnsupportedOperationException("FloatingPoint theory is not supported by Princess");
  }

  @Override
  public PrincessTermType getArrayType(PrincessTermType pIndexType, PrincessTermType pElementType) {
    // no special cases here, princess does only support int arrays with int indexes
    return PrincessTermType.Array;
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(final T pFormula) {
    if (pFormula instanceof ArrayFormula<?, ?>) {
      final FormulaType<?> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<?, ?>) pFormula);
      final FormulaType<?> arrayElementType =
          getArrayFormulaElementType((ArrayFormula<?, ?>) pFormula);
      return (FormulaType<T>) new ArrayFormulaType<>(arrayIndexType, arrayElementType);
    }

    return super.getFormulaType(pFormula);
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, final Formula f, final IExpression input) {
    if (input instanceof IIntLit) {
      IdealInt value = ((IIntLit) input).value();
      return visitor.visitConstant(f, value.bigIntValue());
    } else if (input instanceof IBoolLit) {
      IBoolLit literal = (IBoolLit) input;
      return visitor.visitConstant(f, literal.value());
    } else if (PrincessUtil.isQuantifier(input)) {
      BooleanFormula body = encapsulateBoolean(PrincessUtil.getQuantifierBody(input));
      return visitor.visitQuantifier(
          (BooleanFormula) f,
          PrincessUtil.isForall(input) ? Quantifier.FORALL : Quantifier.EXISTS,

          // Princess does not hold any metadata about bound variables,
          // so we can't get meaningful list here.
          // HOWEVER, passing this list to QuantifiedFormulaManager#mkQuantifier
          // works as expected.
          new ArrayList<Formula>(),
          body);
    } else if (PrincessUtil.isBoundByQuantifier(input)) {
      return visitor.visitBoundVariable(f, PrincessUtil.getIndex(input));
    } else if (PrincessUtil.isVariable(input)) {
      return visitor.visitFreeVariable(f, input.toString());
    } else {
      int arity = input.length();
      String name;
      if (PrincessUtil.isUF(input)) {
        name = ((IFunApp) input).fun().name();
      } else {
        name = toString();
      }
      List<Formula> args = new ArrayList<>(arity);
      for (int i = 0; i < arity; i++) {
        IExpression arg = input.apply(i);
        FormulaType<?> argumentType = getFormulaType(arg);
        args.add(encapsulate(argumentType, arg));
      }

      // Any function application.
      Function<List<Formula>, Formula> constructor =
          new Function<List<Formula>, Formula>() {
            @Override
            public Formula apply(List<Formula> formulas) {
              return encapsulateWithTypeOf(PrincessUtil.replaceArgs(input, extractInfo(formulas)));
            }
          };
      return visitor.visitFunction(
          f, args, FunctionDeclaration.of(name, getDeclarationKind(input)), constructor);
    }
  }

  private FunctionDeclarationKind getDeclarationKind(IExpression input) {
    if (PrincessUtil.isIfThenElse(input)) {
      return FunctionDeclarationKind.ITE;
    } else if (PrincessUtil.isUF(input)) {
      return FunctionDeclarationKind.UF;
    } else if (PrincessUtil.isAnd(input)) {
      return FunctionDeclarationKind.AND;
    } else if (PrincessUtil.isOr(input)) {
      return FunctionDeclarationKind.OR;
    } else if (PrincessUtil.isNot(input)) {
      return FunctionDeclarationKind.NOT;
    } else if (PrincessUtil.isEquivalence(input)) {
      return FunctionDeclarationKind.IFF;
    } else if (PrincessUtil.isIfThenElse(input)) {
      return FunctionDeclarationKind.ITE;
    } else if (PrincessUtil.isVariable(input)) {
      return FunctionDeclarationKind.VAR;
    } else {

      // TODO: other cases!!!
      return FunctionDeclarationKind.OTHER;
    }
  }

  public IExpression makeFunction(IFunction funcDecl, List<IExpression> args) {
    checkArgument(args.size() == funcDecl.arity(), "functiontype has different number of args.");

    final ArrayBuffer<ITerm> argsBuf = new ArrayBuffer<>();
    for (IExpression arg : args) {
      ITerm termArg;
      if (arg instanceof IFormula) { // boolean term -> build ITE(t,0,1)
        termArg = new ITermITE((IFormula) arg, new IIntLit(ZERO()), new IIntLit(ONE()));
      } else {
        termArg = (ITerm) arg;
      }
      argsBuf.$plus$eq(termArg);
    }

    IExpression returnFormula = new IFunApp(funcDecl, argsBuf.toSeq());
    PrincessTermType returnType = environment.getReturnTypeForFunction(funcDecl);

    // boolean term, so we have to use the fun-applier instead of the function itself
    if (returnType == PrincessTermType.Boolean) {
      BooleanFunApplier ap = new BooleanFunApplier(funcDecl);
      return ap.apply(argsBuf);

    } else if (returnType == PrincessTermType.Integer) {
      return returnFormula;
    } else {
      throw new AssertionError(
          "Not possible to have return types for functions other than bool or int.");
    }
  }
}
