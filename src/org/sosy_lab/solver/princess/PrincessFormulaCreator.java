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
import static org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier.EXISTS;
import static org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier.FORALL;
import static scala.collection.JavaConversions.asScalaBuffer;

import ap.basetypes.IdealInt;
import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IBoolLit;
import ap.parser.IConstant;
import ap.parser.IEpsilon;
import ap.parser.IExpression;
import ap.parser.IExpression.BooleanFunApplier;
import ap.parser.IFormula;
import ap.parser.IFormulaITE;
import ap.parser.IFunApp;
import ap.parser.IFunction;
import ap.parser.IIntFormula;
import ap.parser.IIntLit;
import ap.parser.IIntRelation;
import ap.parser.INot;
import ap.parser.IPlus;
import ap.parser.IQuantified;
import ap.parser.ITerm;
import ap.parser.ITermITE;
import ap.parser.ITimes;
import ap.parser.IVariable;
import ap.terfor.conjunctions.Quantifier;

import com.google.common.base.Function;

import org.sosy_lab.solver.api.ArrayFormula;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.FunctionDeclarationKind;
import org.sosy_lab.solver.basicimpl.FormulaCreator;
import org.sosy_lab.solver.visitors.FormulaVisitor;

import scala.Enumeration;
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
    } else if (pFormula instanceof IFormula) {
      return FormulaType.BooleanType;
    } else if (pFormula instanceof ITerm) {
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

  private String getName(IExpression input) {
    if (input instanceof IAtom || input instanceof IConstant) {
      return input.toString();
    } else if (input instanceof IBinFormula) {
      return ((IBinFormula) input).j().toString();
    } else if (input instanceof IFormulaITE || input instanceof ITermITE) {
      // in princess ite representation is the complete formula which we do not want here
      return "ite";
    } else if (input instanceof IIntFormula) {
      return ((IIntFormula) input).rel().toString();
    } else if (input instanceof INot) {
      // in princess not representation is the complete formula which we do not want here
      return "not";
    } else if (input instanceof IFunApp) {
      return ((IFunApp) input).fun().name();
    } else if (input instanceof IPlus) {
      // in princess plus representation is the complete formula which we do not want here
      return "+";
    } else if (input instanceof ITimes) {
      // in princess times representation is the complete formula which we do not want here
      return "*";
    } else if (input instanceof IEpsilon) {
      // in princess epsilon representation is the complete formula which we do not want here
      return "eps";
    } else {
      throw new AssertionError("Unhandled type " + input.getClass());
    }
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, final Formula f, final IExpression input) {
    if (input instanceof IIntLit) {
      IdealInt value = ((IIntLit) input).value();
      return visitor.visitConstant(f, value.bigIntValue());

    } else if (input instanceof IBoolLit) {
      IBoolLit literal = (IBoolLit) input;
      return visitor.visitConstant(f, literal.value());

      // this is a quantifier
    } else if (input instanceof IQuantified) {

      BooleanFormula body = encapsulateBoolean(((IQuantified) input).subformula());
      return visitor.visitQuantifier(
          (BooleanFormula) f,
          ((IQuantified) input).quan().equals(Quantifier.apply(true)) ? FORALL : EXISTS,

          // Princess does not hold any metadata about bound variables,
          // so we can't get meaningful list here.
          // HOWEVER, passing this list to QuantifiedFormulaManager#mkQuantifier
          // works as expected.
          new ArrayList<Formula>(),
          body);

      // variable bound by a quantifier
    } else if (input instanceof IVariable) {
      return visitor.visitBoundVariable(f, ((IVariable) input).index());

      // atom and constant are variables
    } else if (input instanceof IAtom || input instanceof IConstant) {
      return visitor.visitFreeVariable(f, input.toString());

    } else {
      int arity = input.length();
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
              // replace arguments of function
              return encapsulateWithTypeOf(input.update(asScalaBuffer(extractInfo(formulas))));
            }
          };

      return visitor.visitFunction(
          f, args, FunctionDeclaration.of(getName(input), getDeclarationKind(input)), constructor);
    }
  }

  private FunctionDeclarationKind getDeclarationKind(IExpression input) {
    assert !(input instanceof IAtom || input instanceof IConstant)
        : "Variables should be handled somewhere else";

    if (input instanceof IFormulaITE || input instanceof ITermITE) {
      return FunctionDeclarationKind.ITE;
    } else if (input instanceof IFunApp) {
      if (((IFunApp) input).fun().name().equals("select")) {
        return FunctionDeclarationKind.SELECT;
      } else if (((IFunApp) input).fun().name().equals("store")) {
        return FunctionDeclarationKind.STORE;
      }
      return FunctionDeclarationKind.UF;
    } else if (isBinaryFunction(input, IBinJunctor.And())) {
      return FunctionDeclarationKind.AND;
    } else if (isBinaryFunction(input, IBinJunctor.Or())) {
      return FunctionDeclarationKind.OR;
    } else if (input instanceof INot) {
      return FunctionDeclarationKind.NOT;
    } else if (isBinaryFunction(input, IBinJunctor.Eqv())) {
      return FunctionDeclarationKind.IFF;
    } else if (input instanceof ITimes) {
      return FunctionDeclarationKind.MUL;
    } else if (input instanceof IPlus) {
      // SUB does not exist in princess a - b is a + (-b) there
      return FunctionDeclarationKind.ADD;
    } else if (input instanceof IIntFormula) {
      IIntFormula f = (IIntFormula) input;
      if (f.rel().equals(IIntRelation.EqZero())) {
        return FunctionDeclarationKind.EQ;
      } else if (f.rel().equals(IIntRelation.GeqZero())) {
        return FunctionDeclarationKind.GTE;
      } else {
        throw new AssertionError("Unhandled value for integer relation");
      }

    } else {
      // we cannot handle XOR, IMPLIES, DISTINCT, DIV, MODULO, LT, LTE GT in princess
      // they are either handled implicitly by the above mentioned parts or not at all
      return FunctionDeclarationKind.OTHER;
    }
  }

  private static boolean isBinaryFunction(IExpression t, Enumeration.Value val) {
    return (t instanceof IBinFormula) && val == ((IBinFormula) t).j(); // j is the operator
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
