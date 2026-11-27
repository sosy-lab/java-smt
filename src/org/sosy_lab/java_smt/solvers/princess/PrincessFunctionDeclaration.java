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
import ap.parser.IExpression;
import ap.parser.IExpression.BooleanFunApplier;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IFunction;
import ap.parser.IIntLit;
import ap.parser.ITerm;
import ap.parser.ITermITE;
import ap.parser.SMTParser2InputAbsy.SMTFunctionType;
import ap.terfor.preds.Predicate;
import ap.theories.arrays.ExtArray.ArraySort;
import ap.theories.bitvectors.ModuloArithmetic$;
import ap.theories.nia.GroebnerMultiplication;
import ap.theories.rationals.Rationals;
import ap.types.Sort;
import ap.types.Sort$;
import ap.types.Sort.MultipleValueBool$;
import ap.types.SortedIFunction$;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.java_smt.api.FormulaType;
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
abstract sealed class PrincessFunctionDeclaration {
  private PrincessFunctionDeclaration() {}

  public abstract IExpression makeApp(PrincessEnvironment environment, List<IExpression> args);

  public abstract String getName();

  public abstract FunctionDeclarationKind getKind();

  private abstract static sealed class AbstractDeclaration<T> extends PrincessFunctionDeclaration {

    /* some object representing the function declaration. */
    final T declarationItem;

    AbstractDeclaration(T pDeclaration) {
      declarationItem = pDeclaration;
    }

    @Override
    public boolean equals(Object o) {
      return o instanceof AbstractDeclaration<?> other
          && declarationItem.equals(other.declarationItem);
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

  static final class PrincessIFunctionDeclaration extends AbstractDeclaration<IFunction> {
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

    PrincessIFunctionDeclaration(IFunction pFunction, SMTFunctionType pType) {
      super(pFunction);

      ImmutableList.Builder<FormulaType<?>> builder = ImmutableList.builder();
      for (int i = 0; i < pType.arguments().size(); i++) {
        builder.add(
            PrincessEnvironment.getFormulaTypeFromSort(pType.arguments().apply(i).toSort()));
      }

      argSorts = builder.build();
      returnSort = PrincessEnvironment.getFormulaTypeFromSort(pType.result().toSort());
      function = pFunction;
    }

    PrincessIFunctionDeclaration(IFunApp pApp) {
      super(pApp.fun());

      ImmutableList.Builder<FormulaType<?>> builder = ImmutableList.builder();
      for (int i = 0; i < pApp.fun().arity(); i++) {
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
      final List<ITerm> argsList = new ArrayList<>();
      for (int i = 0; i < args.size(); i++) {
        final IExpression arg = args.get(i);
        final ITerm termArg;

        final FormulaType<?> actualType = PrincessEnvironment.getFormulaType(arg);
        final FormulaType<?> expectedType = argSorts.get(i);

        if (actualType.isBooleanType()) {
          // boolean term -> build ITE(t,0,1)
          termArg =
              new ITermITE(
                  (IFormula) arg, new IIntLit(IdealInt.ZERO()), new IIntLit(IdealInt.ONE()));
        } else if (actualType.isIntegerType() && expectedType.isRationalType()) {
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
      if (returnType == MultipleValueBool$.MODULE$) {
        BooleanFunApplier ap = new BooleanFunApplier(function);
        return ap.apply(argsBuf);
      } else {
        return returnFormula;
      }
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

  static final class PrincessByExampleDeclaration extends AbstractDeclaration<IExpression> {

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

  static final class PrincessConstArrayDeclaration extends AbstractDeclaration<ArraySort> {

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

  static final class PrincessBitvectorToBooleanDeclaration extends AbstractDeclaration<Predicate> {

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

  static final class PrincessBitvectorToBitvectorDeclaration
      extends AbstractDeclaration<IFunction> {

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

  static final class PrincessEquationDeclaration extends PrincessFunctionDeclaration {

    static final PrincessEquationDeclaration INSTANCE = new PrincessEquationDeclaration();

    private PrincessEquationDeclaration() {}

    @Override
    public IExpression makeApp(PrincessEnvironment env, List<IExpression> args) {
      checkArgument(args.size() == 2);
      var left = (ITerm) args.get(0);
      var right = (ITerm) args.get(1);
      if (right instanceof IIntLit rightLit && rightLit.value().isZero()) {
        return IExpression.eqZero(left);
      } else {
        return left.$eq$eq$eq(right);
      }
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

  static final class PrincessBitvectorFromIntegerDeclaration extends PrincessFunctionDeclaration {
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

  static final class PrincessBitvectorToIntegerDeclaration extends PrincessFunctionDeclaration {
    static final PrincessBitvectorToIntegerDeclaration SIGNED =
        new PrincessBitvectorToIntegerDeclaration(true);
    static final PrincessBitvectorToIntegerDeclaration UNSIGNED =
        new PrincessBitvectorToIntegerDeclaration(false);

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

  static final class PrincessBitvectorExtendDeclaration extends PrincessFunctionDeclaration {
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

  static final class PrincessMultiplyDeclaration extends PrincessFunctionDeclaration {

    static final PrincessMultiplyDeclaration INSTANCE = new PrincessMultiplyDeclaration();

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

  static final class PrincessRationalMultiplyDeclaration extends PrincessFunctionDeclaration {

    static final PrincessRationalMultiplyDeclaration INSTANCE =
        new PrincessRationalMultiplyDeclaration();

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

  static final class PrincessRationalDivisionDeclaration extends PrincessFunctionDeclaration {
    static final PrincessRationalDivisionDeclaration INSTANCE =
        new PrincessRationalDivisionDeclaration();

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

  static final class PrincessRationalFloorDeclaration extends PrincessFunctionDeclaration {
    static final PrincessRationalFloorDeclaration INSTANCE = new PrincessRationalFloorDeclaration();

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

  static final class PrincessIntegerDivisionDeclaration extends PrincessFunctionDeclaration {
    static final PrincessIntegerDivisionDeclaration INSTANCE =
        new PrincessIntegerDivisionDeclaration();

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

  static final class PrincessIntegerModuloDeclaration extends PrincessFunctionDeclaration {
    static final PrincessIntegerModuloDeclaration INSTANCE = new PrincessIntegerModuloDeclaration();

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

  static final class PrincessModularCongruenceDeclaration extends PrincessFunctionDeclaration {
    static final PrincessModularCongruenceDeclaration INSTANCE =
        new PrincessModularCongruenceDeclaration();

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

  static final class PrincessBitvectorExtractDeclaration extends PrincessFunctionDeclaration {
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

  static final class PrincessBitvectorConcatDeclaration extends PrincessFunctionDeclaration {

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

  static final class PrincessStringRangeDeclaration extends PrincessFunctionDeclaration {
    static final PrincessStringRangeDeclaration INSTANCE = new PrincessStringRangeDeclaration();

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
