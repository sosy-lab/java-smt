// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.solvers.princess.PrincessEnvironment.toITermSeq;
import static org.sosy_lab.java_smt.solvers.princess.PrincessEnvironment.toSeq;

import ap.basetypes.IdealInt;
import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
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
import ap.theories.arrays.ExtArray.ArraySort;
import ap.theories.bitvectors.ModuloArithmetic$;
import ap.theories.nia.GroebnerMultiplication;
import ap.theories.rationals.Rationals;
import ap.types.MonoSortedIFunction;
import ap.types.Sort;
import ap.types.Sort$;
import ap.types.Sort.MultipleValueBool$;
import ap.types.SortedConstantTerm;
import ap.types.SortedIFunction$;
import com.google.common.base.Preconditions;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import scala.Option;
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

  public abstract IExpression makeApp(PrincessEnvironment environment, List<IExpression> args);

  public abstract String getName();

  public abstract FunctionDeclarationKind getKind();

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
    public abstract IExpression makeApp(PrincessEnvironment env, List<IExpression> args);

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

    PrincessIFunctionDeclaration(IFunction pApp) {
      super(pApp);
    }

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {

      // TODO: check argument types
      checkArgument(
          args.size() == declarationItem.arity(), "functiontype has different number of args.");

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
      IFunApp returnFormula = new IFunApp(declarationItem, argsBuf);
      Sort returnType = SortedIFunction$.MODULE$.iResultSort(declarationItem, returnFormula.args());

      // boolean term, so we have to use the fun-applier instead of the function itself
      if (returnType == MultipleValueBool$.MODULE$) {
        BooleanFunApplier ap = new BooleanFunApplier(declarationItem);
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
      if (declarationItem instanceof MonoSortedIFunction) {
        Sort sort = ((MonoSortedIFunction) declarationItem).argSorts().apply(index);
        return PrincessEnvironment.rationalTheory.FractionSort().equals(sort);
      }
      return false;
    }

    @Override
    public String getName() {
      return declarationItem.name();
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.UF;
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

    @Override
    public String getName() {
      throw new UnsupportedOperationException();
    }

    @Override
    public FunctionDeclarationKind getKind() {
      throw new UnsupportedOperationException();
    }
  }

  static class PrincessConstArrayDeclaration extends AbstractDeclaration<ArraySort> {

    PrincessConstArrayDeclaration(PrincessEnvironment env, IFunApp pArray) {
      super((ArraySort) Sort$.MODULE$.sortOf(pArray));
      env.cacheConstArray(declarationItem, pArray.apply(0), pArray);
    }

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 1);
      return env.makeConstArray(declarationItem, (ITerm) args.get(0));
    }

    @Override
    public String getName() {
      return "const";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.CONST;
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

    @Override
    public String getName() {
      throw new UnsupportedOperationException();
    }

    @Override
    public FunctionDeclarationKind getKind() {
      throw new UnsupportedOperationException();
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

    @Override
    public String getName() {
      throw new UnsupportedOperationException();
    }

    @Override
    public FunctionDeclarationKind getKind() {
      throw new UnsupportedOperationException();
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

    @Override
    public String getName() {
      return "=";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.EQ;
    }
  }

  static class PrincessBitvectorFromIntegerDeclaration extends PrincessFunctionDeclaration {
    private final int bitwidth;

    public PrincessBitvectorFromIntegerDeclaration(int pBitwidth) {
      bitwidth = pBitwidth;
    }

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 1);
      return ModuloArithmetic$.MODULE$.cast2UnsignedBV(bitwidth, (ITerm) args.get(0));
    }

    @Override
    public String getName() {
      return "int_to_bv";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.INT_TO_BV;
    }
  }

  static class PrincessBitvectorToIntegerDeclaration extends PrincessFunctionDeclaration {
    static final PrincessBitvectorToIntegerDeclaration SIGNED =
        new PrincessBitvectorToIntegerDeclaration(true) {};
    static final PrincessBitvectorToIntegerDeclaration UNSIGNED =
        new PrincessBitvectorToIntegerDeclaration(false) {};

    private final boolean signed;

    private PrincessBitvectorToIntegerDeclaration(boolean pSigned) {
      signed = pSigned;
    }

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 1);
      ITerm bvFormula = (ITerm) args.get(0);

      final Sort sort = Sort$.MODULE$.sortOf(bvFormula);
      final Option<Object> bitWidth = PrincessEnvironment.getBitWidth(sort);
      Preconditions.checkArgument(bitWidth.isDefined());
      final int size = (Integer) bitWidth.get();

      if (signed) {
        bvFormula = ModuloArithmetic$.MODULE$.cast2SignedBV(size, bvFormula);
      }
      return ModuloArithmetic$.MODULE$.cast2Int(bvFormula);
    }

    @Override
    public String getName() {
      return signed ? "sbv_to_int" : "ubv_to_int";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return signed ? FunctionDeclarationKind.SBV_TO_INT : FunctionDeclarationKind.UBV_TO_INT;
    }
  }

  static class PrincessBitvectorExtendDeclaration extends PrincessFunctionDeclaration {
    private final int extensionBits;
    private final boolean signed;

    PrincessBitvectorExtendDeclaration(int pExtensionBits, boolean pSigned) {
      extensionBits = pExtensionBits;
      signed = pSigned;
    }

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 1);
      if (signed) {
        return ModuloArithmetic$.MODULE$.sign_extend(extensionBits, (ITerm) args.get(0));
      } else {
        return ModuloArithmetic$.MODULE$.zero_extend(extensionBits, (ITerm) args.get(0));
      }
    }

    @Override
    public String getName() {
      return signed ? "sign_extend" : "zero_extend";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return signed
          ? FunctionDeclarationKind.BV_SIGN_EXTENSION
          : FunctionDeclarationKind.BV_ZERO_EXTENSION;
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

    @Override
    public String getName() {
      return "mul";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.MUL;
    }
  }

  static class PrincessRationalMultiplyDeclaration extends PrincessFunctionDeclaration {

    static final PrincessRationalMultiplyDeclaration INSTANCE =
        new PrincessRationalMultiplyDeclaration() {};

    private PrincessRationalMultiplyDeclaration() {}

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 2);
      return Rationals.mul((ITerm) args.get(0), (ITerm) args.get(1));
    }

    @Override
    public String getName() {
      return "mul";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.MUL;
    }
  }

  static class PrincessRationalDivisionDeclaration extends PrincessFunctionDeclaration {
    static final PrincessRationalDivisionDeclaration INSTANCE =
        new PrincessRationalDivisionDeclaration() {};

    private PrincessRationalDivisionDeclaration() {}

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 2);
      // SMT-LIB allows division by zero, so we use divWithSpecialZero here.
      // If the divisor is zero, divWithSpecialZero will evaluate to a unary UF `ratDivZero`,
      // otherwise it is the normal division
      return Rationals.divWithSpecialZero((ITerm) args.get(0), (ITerm) args.get(1));
    }

    @Override
    public String getName() {
      return "div";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.DIV;
    }
  }

  static class PrincessRationalFloorDeclaration extends PrincessFunctionDeclaration {
    static final PrincessRationalFloorDeclaration INSTANCE =
        new PrincessRationalFloorDeclaration() {};

    private PrincessRationalFloorDeclaration() {}

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 1);
      return Rationals.ring2int((ITerm) args.get(0));
    }

    @Override
    public String getName() {
      return "floor";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.FLOOR;
    }
  }

  static class PrincessIntegerDivisionDeclaration extends PrincessFunctionDeclaration {
    static final PrincessIntegerDivisionDeclaration INSTANCE =
        new PrincessIntegerDivisionDeclaration() {};

    private PrincessIntegerDivisionDeclaration() {}

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 2);
      return GroebnerMultiplication.eDivWithSpecialZero((ITerm) args.get(0), (ITerm) args.get(1));
    }

    @Override
    public String getName() {
      return "div";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.DIV;
    }
  }

  static class PrincessIntegerModuloDeclaration extends PrincessFunctionDeclaration {
    static final PrincessIntegerModuloDeclaration INSTANCE =
        new PrincessIntegerModuloDeclaration() {};

    private PrincessIntegerModuloDeclaration() {}

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 2);
      return GroebnerMultiplication.eModWithSpecialZero((ITerm) args.get(0), (ITerm) args.get(1));
    }

    @Override
    public String getName() {
      return "mod";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.MODULO;
    }
  }

  static class PrincessModularCongruenceDeclaration extends PrincessFunctionDeclaration {
    static final PrincessModularCongruenceDeclaration INSTANCE =
        new PrincessModularCongruenceDeclaration() {};

    private PrincessModularCongruenceDeclaration() {}

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 3);
      var t1 = (ITerm) args.get(0);
      var t2 = (ITerm) args.get(1);
      var t3 = (ITerm) args.get(2);
      return IExpression.ex(
          IExpression.eqZero(
              t1.$minus(t2).$plus(GroebnerMultiplication.mult(IExpression.v(0), t3))));
    }

    @Override
    public String getName() {
      return "div";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.OTHER;
    }
  }

  static class PrincessBitvectorExtractDeclaration extends PrincessFunctionDeclaration {
    private final int upper;
    private final int lower;

    PrincessBitvectorExtractDeclaration(int pUpper, int pLower) {
      upper = pUpper;
      lower = pLower;
    }

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 1);
      return ModuloArithmetic$.MODULE$.extract(upper, lower, (ITerm) args.get(0));
    }

    @Override
    public String getName() {
      return "extract";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.BV_EXTRACT;
    }
  }

  static class PrincessBitvectorConcatDeclaration extends PrincessFunctionDeclaration {

    PrincessBitvectorConcatDeclaration() {}

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 2);
      return ModuloArithmetic$.MODULE$.concat((ITerm) args.get(0), (ITerm) args.get(1));
    }

    @Override
    public String getName() {
      return "concat";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.BV_CONCAT;
    }
  }

  static class PrincessStringRangeDeclaration extends PrincessFunctionDeclaration {
    static final PrincessStringRangeDeclaration INSTANCE = new PrincessStringRangeDeclaration() {};

    private PrincessStringRangeDeclaration() {}

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 2);
      // Precondition: Both bounds must be single character Strings
      // Princess already checks that the lower bound is smaller than the upper bound and returns
      // the empty language otherwise.
      ITerm one = new IIntLit(IdealInt.apply(1));
      IFormula cond =
          new IBinFormula(
              IBinJunctor.And(),
              new IFunApp(PrincessEnvironment.stringTheory.str_len(), toITermSeq(args.get(0)))
                  .$eq$eq$eq(one),
              new IFunApp(PrincessEnvironment.stringTheory.str_len(), toITermSeq(args.get(1)))
                  .$eq$eq$eq(one));
      return new ITermITE(
          cond,
          new IFunApp(
              PrincessEnvironment.stringTheory.re_range(), toITermSeq(args.get(0), args.get(1))),
          new IFunApp(PrincessEnvironment.stringTheory.re_none(), toITermSeq()));
    }

    @Override
    public String getName() {
      return "range";
    }

    @Override
    public FunctionDeclarationKind getKind() {
      return FunctionDeclarationKind.RE_RANGE;
    }
  }
}
