// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.base.Preconditions.checkArgument;
import static scala.collection.JavaConverters.collectionAsScalaIterableConverter;

import ap.basetypes.IdealInt;
import ap.parser.IExpression;
import ap.parser.IExpression.BooleanFunApplier;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IFunction;
import ap.parser.IIntLit;
import ap.parser.ITerm;
import ap.parser.ITermITE;
import ap.theories.nia.GroebnerMultiplication;
import ap.types.Sort;
import ap.types.SortedIFunction$;
import java.util.ArrayList;
import java.util.List;
import scala.collection.immutable.Seq;

/**
 * Unlike other solvers, Princess does not have a class representing the built-in functions (OR,
 * etc...). This interface wraps two cases: IFunction declaration (represented by IFunction), and
 * declaration for a built-in function (represented by an example instantiation of the built-in
 * function). The latter case does not have a valid {@code equals}, but it is not necessary, as it's
 * not used in {@link org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl}.
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

      // TODO: check argument types
      checkArgument(args.size() == app.arity(), "functiontype has different number of args.");

      final List<ITerm> argsList = new ArrayList<>();
      for (IExpression arg : args) {
        ITerm termArg;
        if (arg instanceof IFormula) { // boolean term -> build ITE(t,0,1)
          termArg =
              new ITermITE(
                  (IFormula) arg, new IIntLit(IdealInt.ZERO()), new IIntLit(IdealInt.ONE()));
        } else {
          termArg = (ITerm) arg;
        }
        argsList.add(termArg);
      }
      final Seq<ITerm> argsBuf = collectionAsScalaIterableConverter(argsList).asScala().toSeq();
      IFunApp returnFormula = new IFunApp(app, argsBuf);
      Sort returnType = SortedIFunction$.MODULE$.iResultSort(app, returnFormula.args());

      // boolean term, so we have to use the fun-applier instead of the function itself
      if (returnType == PrincessEnvironment.BOOL_SORT) {
        BooleanFunApplier ap = new BooleanFunApplier(app);
        return ap.apply(argsBuf);
      } else {
        return returnFormula;
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
    public boolean equals(Object o) {
      if (!(o instanceof PrincessByExampleDeclaration)) {
        return false;
      }
      PrincessByExampleDeclaration other = (PrincessByExampleDeclaration) o;
      return example.equals(other.example);
    }

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      return example.update(collectionAsScalaIterableConverter(args).asScala().toSeq());
    }

    @Override
    public int hashCode() {
      return example.hashCode();
    }

    @Override
    public String toString() {
      return example.toString();
    }
  }

  static class PrincessEquationDeclaration extends PrincessFunctionDeclaration {

    static final PrincessEquationDeclaration INSTANCE = new PrincessEquationDeclaration() {};

    private PrincessEquationDeclaration() {}

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 2);
      return ((ITerm) args.get(0)).$eq$eq$eq((ITerm) args.get(1));
    }
  }

  static class PrincessMultiplyDeclaration extends PrincessFunctionDeclaration {

    static final PrincessMultiplyDeclaration INSTANCE = new PrincessMultiplyDeclaration() {};

    private PrincessMultiplyDeclaration() {}

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 2);
      return GroebnerMultiplication.mult((ITerm) args.get(0), (ITerm) args.get(1));
    }
  }
}
