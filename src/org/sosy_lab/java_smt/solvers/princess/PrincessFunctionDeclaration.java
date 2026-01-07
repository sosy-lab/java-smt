// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.solvers.princess.PrincessEnvironment.toSeq;

import ap.basetypes.IdealInt;
import ap.parser.IAtom;
import ap.parser.IConstant;
import ap.parser.IExpression;
import ap.parser.IExpression.BooleanFunApplier;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IFunction;
import ap.parser.IIntLit;
import ap.parser.ITerm;
import ap.parser.ITermITE;
import ap.terfor.ConstantTerm;
import ap.terfor.preds.Predicate;
import ap.theories.nia.GroebnerMultiplication;
import ap.types.MonoSortedIFunction;
import ap.types.Sort;
import ap.types.Sort$;
import ap.types.SortedConstantTerm;
import ap.types.SortedIFunction$;
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.java_smt.api.FormulaType;
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

  private abstract static class AbstractDeclaration<T> extends PrincessFunctionDeclaration {

    /* some object representing the function declaration. */
    final T declarationItem;

    AbstractDeclaration(T pDeclaration) {
      declarationItem = pDeclaration;
    }

    @Override
    public boolean equals(Object o) {
      if (!(o instanceof AbstractDeclaration<?>)) {
        return false;
      }
      AbstractDeclaration<?> other = (AbstractDeclaration<?>) o;
      return declarationItem.equals(other.declarationItem);
    }

    @Override
    abstract IExpression makeApp(PrincessEnvironment env, List<IExpression> args);

    @Override
    public int hashCode() {
      return declarationItem.hashCode();
    }

    @Override
    public String toString() {
      return declarationItem.toString();
    }
  }

  static class PrincessIFunctionDeclaration extends AbstractDeclaration<IFunction> {
    private final List<FormulaType<?>> argSorts;
    private final FormulaType<?> returnSort;

    private final IFunction function;

    PrincessIFunctionDeclaration(
        List<FormulaType<?>> pArgSorts, FormulaType<?> pReturnSort, IFunction pFunction) {
      super(pFunction);

      argSorts = pArgSorts;
      returnSort = pReturnSort;
      function = pFunction;
    }

    PrincessIFunctionDeclaration(IFunApp pApp) {
      super(pApp.fun());

      ImmutableList.Builder<FormulaType<?>> builder = ImmutableList.builder();
      for (int i = 0; i < pApp.args().length(); i++) {
        builder.add(PrincessEnvironment.getFormulaType(pApp.apply(i)));
      }
      argSorts = builder.build();
      returnSort = PrincessEnvironment.getFormulaType(pApp);
      function = pApp.fun();
    }

    public IFunction getFunction() {
      return function;
    }

    public List<FormulaType<?>> getArgSorts() {
      return argSorts;
    }

    public FormulaType<?> getReturnSort() {
      return returnSort;
    }

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {

      // TODO: check argument types
      checkArgument(args.size() == function.arity(), "functiontype has different number of args.");

      final List<ITerm> argsList = new ArrayList<>();
      for (int i = 0; i < args.size(); i++) {
        final IExpression arg = args.get(i);
        final ITerm termArg;
        if (arg instanceof IFormula) { // boolean term -> build ITE(t,0,1)
          termArg =
              new ITermITE(
                  (IFormula) arg, new IIntLit(IdealInt.ZERO()), new IIntLit(IdealInt.ONE()));
        } else if (!exprIsRational(arg) && functionTakesRational(i)) {
          // sort does not match, so we need  to cast the argument to rational theory.
          termArg = PrincessEnvironment.rationalTheory.int2ring((ITerm) arg);
        } else {
          termArg = (ITerm) arg;
        }
        argsList.add(termArg);
      }
      final Seq<ITerm> argsBuf = toSeq(argsList);
      IFunApp returnFormula = new IFunApp(function, argsBuf);
      Sort returnType = SortedIFunction$.MODULE$.iResultSort(function, returnFormula.args());

      // boolean term, so we have to use the fun-applier instead of the function itself
      if (returnType == PrincessEnvironment.BOOL_SORT) {
        BooleanFunApplier ap = new BooleanFunApplier(function);
        return ap.apply(argsBuf);
      } else {
        return returnFormula;
      }
    }

    /* Check if the expression returns a "Rational". */
    private boolean exprIsRational(IExpression arg) {
      if (arg instanceof IFunApp) {
        IFunction fun = ((IFunApp) arg).fun();
        if (fun instanceof MonoSortedIFunction) {
          Sort sort = ((MonoSortedIFunction) fun).resSort();
          return PrincessEnvironment.FRACTION_SORT.equals(sort);
        }
      }
      if (arg instanceof IConstant) {
        ConstantTerm constant = ((IConstant) arg).c();
        if (constant instanceof SortedConstantTerm) {
          Sort sort = ((SortedConstantTerm) constant).sort();
          return PrincessEnvironment.FRACTION_SORT.equals(sort);
        }
      }
      // TODO: What about other terms?
      return false;
    }

    /* Checks if the k-th argument of the function is a "Rational". */
    private boolean functionTakesRational(Integer index) {
      // we switch from "int" to "Integer" in the signature to avoid ambiguous types with Scala API.
      if (function instanceof MonoSortedIFunction) {
        Sort sort = ((MonoSortedIFunction) function).argSorts().apply(index);
        return PrincessEnvironment.rationalTheory.FractionSort().equals(sort);
      }
      return false;
    }
  }

  static class PrincessByExampleDeclaration extends AbstractDeclaration<IExpression> {

    PrincessByExampleDeclaration(IExpression pExample) {
      super(pExample);
    }

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      return declarationItem.update(toSeq(args));
    }
  }

  static class PrincessBitvectorToBooleanDeclaration extends AbstractDeclaration<Predicate> {

    PrincessBitvectorToBooleanDeclaration(Predicate pPredicate) {
      super(pPredicate);
    }

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      ITerm arg0 = (ITerm) args.get(0);
      Sort sort = Sort$.MODULE$.sortOf(arg0);
      scala.Option<Object> bitWidth = PrincessEnvironment.getBitWidth(sort);
      checkArgument(bitWidth.isDefined(), "BitvectorFormula with actual type %s: %s", sort, arg0);
      int bitsize = (Integer) bitWidth.get();

      List<ITerm> newArgs = new ArrayList<>();
      newArgs.add(new IIntLit(IdealInt.apply(bitsize)));
      for (IExpression arg : args) {
        newArgs.add((ITerm) arg);
      }

      return new IAtom(declarationItem, toSeq(newArgs));
    }
  }

  static class PrincessBitvectorToBitvectorDeclaration extends AbstractDeclaration<IFunction> {

    PrincessBitvectorToBitvectorDeclaration(IFunction pFunction) {
      super(pFunction);
    }

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      ITerm arg0 = (ITerm) args.get(0);
      Sort sort = Sort$.MODULE$.sortOf(arg0);
      scala.Option<Object> bitWidth = PrincessEnvironment.getBitWidth(sort);
      checkArgument(bitWidth.isDefined(), "BitvectorFormula with actual type %s: %s", sort, arg0);
      int bitsize = (Integer) bitWidth.get();

      List<ITerm> newArgs = new ArrayList<>();
      newArgs.add(new IIntLit(IdealInt.apply(bitsize)));
      for (IExpression arg : args) {
        newArgs.add((ITerm) arg);
      }

      return new IFunApp(declarationItem, toSeq(newArgs));
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
