/*
 *
 *  *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  *  This file is part of JavaSMT.
 *  *
 *  *  Copyright (C) 2007-2016  Dirk Beyer
 *  *  All rights reserved.
 *  *
 *  *  Licensed under the Apache License, Version 2.0 (the "License");
 *  *  you may not use this file except in compliance with the License.
 *  *  You may obtain a copy of the License at
 *  *
 *  *      http://www.apache.org/licenses/LICENSE-2.0
 *  *
 *  *  Unless required by applicable law or agreed to in writing, software
 *  *  distributed under the License is distributed on an "AS IS" BASIS,
 *  *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  *  See the License for the specific language governing permissions and
 *  *  limitations under the License.
 *
 *
 */

package org.sosy_lab.solver.princess;

import static com.google.common.base.Preconditions.checkArgument;

import ap.basetypes.IdealInt;
import ap.parser.IExpression;
import ap.parser.IExpression.BooleanFunApplier;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IFunction;
import ap.parser.IIntLit;
import ap.parser.ITerm;
import ap.parser.ITermITE;

import scala.collection.mutable.ArrayBuffer;

import java.util.List;

/**
 * Unlike other solvers, Princess does not have a class representing the
 * built-in functions (OR, etc...).
 * This interface wraps two cases:  IFunction declaration (represented by IFunction),
 * and declaration for a built-in function (represented by an example instantiation of the
 * built-in function).
 * The latter case does not have a valid {@code equals}, but it is not necessary,
 * as it's not used in {@link org.sosy_lab.solver.basicimpl.FunctionDeclarationImpl}.
 */
abstract class PrincessFunctionDeclaration {
  private PrincessFunctionDeclaration() {}

  abstract IExpression makeApp(PrincessEnvironment environment, List<IExpression> args);

  static class PrincessIFunctionDeclaration extends PrincessFunctionDeclaration {
    private final IFunction app;

    PrincessIFunctionDeclaration(IFunction pApp) {
      app = pApp;
    }

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {

      checkArgument(args.size() == app.arity(), "functiontype has different number of args.");

      final ArrayBuffer<ITerm> argsBuf = new ArrayBuffer<>();
      for (IExpression arg : args) {
        ITerm termArg;
        if (arg instanceof IFormula) { // boolean term -> build ITE(t,0,1)
          termArg =
              new ITermITE(
                  (IFormula) arg, new IIntLit(IdealInt.ZERO()), new IIntLit(IdealInt.ONE()));
        } else {
          termArg = (ITerm) arg;
        }
        argsBuf.$plus$eq(termArg);
      }
      IExpression returnFormula = new IFunApp(app, argsBuf.toSeq());
      PrincessTermType returnType = env.getReturnTypeForFunction(app);

      // boolean term, so we have to use the fun-applier instead of the function itself
      if (returnType == PrincessTermType.Boolean) {
        BooleanFunApplier ap = new BooleanFunApplier(app);
        return ap.apply(argsBuf);

      } else if (returnType == PrincessTermType.Integer) {
        return returnFormula;
      } else {
        throw new AssertionError(
            "Not possible to have return types for functions other than bool or int.");
      }
    }

    @Override
    public boolean equals(Object o) {
      if (!(o instanceof PrincessIFunctionDeclaration)) {
        return false;
      }
      PrincessIFunctionDeclaration other = (PrincessIFunctionDeclaration) o;
      return app.equals(other.app);
    }

    @Override
    public int hashCode() {
      return app.hashCode();
    }

    @Override
    public String toString() {
      return app.toString();
    }
  }

  static class PrincessByExampleDeclaration extends PrincessFunctionDeclaration {
    private final IExpression example;

    PrincessByExampleDeclaration(IExpression pExample) {
      example = pExample;
    }

    @Override
    public IExpression makeApp(
        PrincessEnvironment env, List<IExpression> args) {
      return example.update(scala.collection.JavaConversions.asScalaBuffer(args));
    }
  }

}
