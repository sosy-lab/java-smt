// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier.EXISTS;
import static org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier.FORALL;
import static org.sosy_lab.java_smt.solvers.princess.PrincessEnvironment.toSeq;
import static scala.collection.JavaConverters.asJava;

import ap.basetypes.IdealInt;
import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IBoolLit;
import ap.parser.IConstant;
import ap.parser.IEpsilon;
import ap.parser.IEquation;
import ap.parser.IExpression;
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
import ap.terfor.preds.Predicate;
import ap.theories.ExtArray;
import ap.theories.bitvectors.ModuloArithmetic;
import ap.theories.nia.GroebnerMultiplication$;
import ap.types.Sort;
import ap.types.Sort$;
import ap.types.Sort.MultipleValueBool$;
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessByExampleDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessEquationDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessIFunctionDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessMultiplyDeclaration;
import scala.Enumeration;
import scala.collection.immutable.Seq;

class PrincessFormulaCreator
    extends FormulaCreator<IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  // Hash-maps from interpreted functions and predicates to their corresponding
  // Java-SMT kind
  private static final Map<IFunction, FunctionDeclarationKind> theoryFunctionKind = new HashMap<>();
  private static final Map<Predicate, FunctionDeclarationKind> theoryPredKind = new HashMap<>();

  static {
    theoryFunctionKind.put(ModuloArithmetic.bv_concat(), FunctionDeclarationKind.BV_CONCAT);
    theoryFunctionKind.put(ModuloArithmetic.bv_extract(), FunctionDeclarationKind.BV_EXTRACT);
    theoryFunctionKind.put(ModuloArithmetic.bv_not(), FunctionDeclarationKind.BV_NOT);
    theoryFunctionKind.put(ModuloArithmetic.bv_neg(), FunctionDeclarationKind.BV_NEG);
    theoryFunctionKind.put(ModuloArithmetic.bv_and(), FunctionDeclarationKind.BV_AND);
    theoryFunctionKind.put(ModuloArithmetic.bv_or(), FunctionDeclarationKind.BV_OR);
    theoryFunctionKind.put(ModuloArithmetic.bv_add(), FunctionDeclarationKind.BV_ADD);
    theoryFunctionKind.put(ModuloArithmetic.bv_sub(), FunctionDeclarationKind.BV_SUB);
    theoryFunctionKind.put(ModuloArithmetic.bv_mul(), FunctionDeclarationKind.BV_MUL);
    theoryFunctionKind.put(ModuloArithmetic.bv_udiv(), FunctionDeclarationKind.BV_UDIV);
    theoryFunctionKind.put(ModuloArithmetic.bv_sdiv(), FunctionDeclarationKind.BV_SDIV);
    theoryFunctionKind.put(ModuloArithmetic.bv_urem(), FunctionDeclarationKind.BV_UREM);
    theoryFunctionKind.put(ModuloArithmetic.bv_srem(), FunctionDeclarationKind.BV_SREM);
    // modmod.bv_smod()?
    theoryFunctionKind.put(ModuloArithmetic.bv_shl(), FunctionDeclarationKind.BV_SHL);
    theoryFunctionKind.put(ModuloArithmetic.bv_lshr(), FunctionDeclarationKind.BV_LSHR);
    theoryFunctionKind.put(ModuloArithmetic.bv_ashr(), FunctionDeclarationKind.BV_ASHR);
    theoryFunctionKind.put(ModuloArithmetic.bv_xor(), FunctionDeclarationKind.BV_XOR);
    // modmod.bv_xnor()?
    // modmod.bv_comp()?

    // casts to integer, sign/zero-extension?

    theoryPredKind.put(ModuloArithmetic.bv_ult(), FunctionDeclarationKind.BV_ULT);
    theoryPredKind.put(ModuloArithmetic.bv_ule(), FunctionDeclarationKind.BV_ULE);
    theoryPredKind.put(ModuloArithmetic.bv_slt(), FunctionDeclarationKind.BV_SLT);
    theoryPredKind.put(ModuloArithmetic.bv_sle(), FunctionDeclarationKind.BV_SLE);

    theoryFunctionKind.put(GroebnerMultiplication$.MODULE$.mul(), FunctionDeclarationKind.MUL);
  }

  PrincessFormulaCreator(PrincessEnvironment pEnv) {
    super(pEnv, PrincessEnvironment.BOOL_SORT, PrincessEnvironment.INTEGER_SORT, null);
  }

  @Override
  public Object convertValue(IExpression value) {
    if (value instanceof IBoolLit) {
      return ((IBoolLit) value).value();
    } else if (value instanceof IIntLit) {
      return ((IIntLit) value).value().bigIntValue();
    }
    if (value instanceof IFunApp) {
      IFunApp fun = (IFunApp) value;
      switch (fun.fun().name()) {
        case "false":
          assert fun.fun().arity() == 0;
          return false;
        case "mod_cast":
          // we found a bitvector BV(lower, upper, ctxt), lets extract the last parameter
          return ((IIntLit) fun.apply(2)).value().bigIntValue();
        default:
      }
    }

    throw new IllegalArgumentException(
        "unhandled model value " + value + " of type " + value.getClass());
  }

  @Override
  public FormulaType<?> getFormulaType(IExpression pFormula) {
    if (pFormula instanceof IFormula) {
      return FormulaType.BooleanType;
    } else if (pFormula instanceof ITerm) {
      final Sort sort = Sort$.MODULE$.sortOf((ITerm) pFormula);
      return getFormulaTypeFromSort(sort);
    }
    throw new IllegalArgumentException(
        String.format(
            "Unknown formula type '%s' for formula '%s'.", pFormula.getClass(), pFormula));
  }

  private FormulaType<?> getFormulaTypeFromSort(final Sort sort) {
    if (sort == PrincessEnvironment.BOOL_SORT) {
      return FormulaType.BooleanType;
    } else if (sort == PrincessEnvironment.INTEGER_SORT) {
      return FormulaType.IntegerType;
    } else if (sort instanceof ExtArray.ArraySort) {
      Seq<Sort> indexSorts = ((ExtArray.ArraySort) sort).theory().indexSorts();
      Sort elementSort = ((ExtArray.ArraySort) sort).theory().objSort();
      assert indexSorts.iterator().size() == 1 : "unexpected index type in Array type:" + sort;
      // assert indexSorts.size() == 1; // TODO Eclipse does not like simpler code.
      return new ArrayFormulaType<>(
          getFormulaTypeFromSort(indexSorts.iterator().next()), // get single index-sort
          getFormulaTypeFromSort(elementSort));
    } else if (sort instanceof MultipleValueBool$) {
      return FormulaType.BooleanType;
    } else {
      scala.Option<Object> bitWidth = getBitWidth(sort);
      if (bitWidth.isDefined()) {
        return FormulaType.getBitvectorTypeWithSize((Integer) bitWidth.get());
      }
    }
    throw new IllegalArgumentException(
        String.format("Unknown formula type '%s' for sort '%s'.", sort.getClass(), sort));
  }

  static scala.Option<Object> getBitWidth(final Sort sort) {
    scala.Option<Object> bitWidth = ModuloArithmetic.UnsignedBVSort$.MODULE$.unapply(sort);
    if (!bitWidth.isDefined()) {
      bitWidth = ModuloArithmetic.SignedBVSort$.MODULE$.unapply(sort);
    }
    return bitWidth;
  }

  @Override
  public IExpression makeVariable(Sort type, String varName) {
    return getEnv().makeVariable(type, varName);
  }

  @Override
  public Sort getBitvectorType(int pBitwidth) {
    return ModuloArithmetic.UnsignedBVSort$.MODULE$.apply(pBitwidth);
  }

  @Override
  public Sort getFloatingPointType(FormulaType.FloatingPointType type) {
    throw new UnsupportedOperationException("FloatingPoint theory is not supported by Princess");
  }

  @Override
  public Sort getArrayType(Sort pIndexType, Sort pElementType) {
    return new ExtArray(toSeq(ImmutableList.of(pIndexType)), pElementType).sort();
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(final T pFormula) {
    if (pFormula instanceof BitvectorFormula) {
      ITerm input = (ITerm) extractInfo(pFormula);
      Sort sort = Sort$.MODULE$.sortOf(input);
      scala.Option<Object> bitWidth = getBitWidth(sort);
      checkArgument(
          bitWidth.isDefined(), "BitvectorFormula with actual type %s: %s", sort, pFormula);
      return (FormulaType<T>) FormulaType.getBitvectorTypeWithSize((Integer) bitWidth.get());

    } else if (pFormula instanceof ArrayFormula<?, ?>) {
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
    } else if (input instanceof IEquation) {
      return "=";
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
          new ArrayList<>(),
          body);

      // variable bound by a quantifier
    } else if (input instanceof IVariable) {
      return visitor.visitBoundVariable(f, ((IVariable) input).index());

      // nullary atoms and constant are variables
    } else if (((input instanceof IAtom) && asJava(((IAtom) input).args()).isEmpty())
        || input instanceof IConstant) {
      return visitor.visitFreeVariable(f, input.toString());

      // Princess encodes multiplication as "linear coefficient and factor" with arity 1.
    } else if (input instanceof ITimes) {
      assert input.length() == 1;

      ITimes multiplication = (ITimes) input;
      IIntLit coeff = new IIntLit(multiplication.coeff());
      FormulaType<IntegerFormula> coeffType = FormulaType.IntegerType;
      IExpression factor = multiplication.subterm();
      FormulaType<?> factorType = getFormulaType(factor);

      return visitor.visitFunction(
          f,
          ImmutableList.of(encapsulate(coeffType, coeff), encapsulate(factorType, factor)),
          FunctionDeclarationImpl.of(
              getName(input),
              getDeclarationKind(input),
              ImmutableList.of(coeffType, factorType),
              getFormulaType(f),
              PrincessMultiplyDeclaration.INSTANCE));

    } else {

      // then we have to check the declaration kind
      final FunctionDeclarationKind kind = getDeclarationKind(input);

      if (kind == FunctionDeclarationKind.EQ) {
        scala.Option<scala.Tuple2<ITerm, ITerm>> maybeArgs =
            IExpression.Eq$.MODULE$.unapply((IFormula) input);

        assert maybeArgs.isDefined();

        final ITerm left = maybeArgs.get()._1;
        final ITerm right = maybeArgs.get()._2;

        ImmutableList.Builder<Formula> args = ImmutableList.builder();
        ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();

        FormulaType<?> argumentTypeLeft = getFormulaType(left);
        args.add(encapsulate(argumentTypeLeft, left));
        argTypes.add(argumentTypeLeft);
        FormulaType<?> argumentTypeRight = getFormulaType(right);
        args.add(encapsulate(argumentTypeRight, right));
        argTypes.add(argumentTypeRight);

        return visitor.visitFunction(
            f,
            args.build(),
            FunctionDeclarationImpl.of(
                getName(input),
                FunctionDeclarationKind.EQ,
                argTypes.build(),
                getFormulaType(f),
                PrincessEquationDeclaration.INSTANCE));

      } else if (kind == FunctionDeclarationKind.UF && input instanceof IIntFormula) {

        assert ((IIntFormula) input).rel().equals(IIntRelation.EqZero());

        // this is really a Boolean formula, visit the lhs of the equation
        return visit(visitor, f, ((IIntFormula) input).t());

      } else {

        ImmutableList.Builder<Formula> args = ImmutableList.builder();
        ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();
        int arity = input.length();
        for (int i = 0; i < arity; i++) {
          IExpression arg = input.apply(i);
          FormulaType<?> argumentType = getFormulaType(arg);
          args.add(encapsulate(argumentType, arg));
          argTypes.add(argumentType);
        }

        PrincessFunctionDeclaration solverDeclaration;

        if (input instanceof IFunApp) {
          if (kind == FunctionDeclarationKind.UF) {
            solverDeclaration = new PrincessIFunctionDeclaration(((IFunApp) input).fun());
          } else if (kind == FunctionDeclarationKind.MUL) {
            solverDeclaration = PrincessMultiplyDeclaration.INSTANCE;
          } else {
            solverDeclaration = new PrincessByExampleDeclaration(input);
          }
        } else {
          solverDeclaration = new PrincessByExampleDeclaration(input);
        }

        return visitor.visitFunction(
            f,
            args.build(),
            FunctionDeclarationImpl.of(
                getName(input), kind, argTypes.build(), getFormulaType(f), solverDeclaration));
      }
    }
  }

  private FunctionDeclarationKind getDeclarationKind(IExpression input) {
    assert !(((input instanceof IAtom) && asJava(((IAtom) input).args()).isEmpty())
            || input instanceof IConstant)
        : "Variables should be handled somewhere else";

    if (input instanceof IFormulaITE || input instanceof ITermITE) {
      return FunctionDeclarationKind.ITE;
    } else if (input instanceof IFunApp) {
      final IFunction fun = ((IFunApp) input).fun();
      final FunctionDeclarationKind theoryKind = theoryFunctionKind.get(fun);
      if (theoryKind != null) {
        return theoryKind;
      } else if (ExtArray.Select$.MODULE$.unapply(fun).isDefined()) {
        return FunctionDeclarationKind.SELECT;
      } else if (ExtArray.Store$.MODULE$.unapply(fun).isDefined()) {
        return FunctionDeclarationKind.STORE;
      } else {
        return FunctionDeclarationKind.UF;
      }
    } else if (input instanceof IAtom) {
      final Predicate pred = ((IAtom) input).pred();
      final FunctionDeclarationKind theoryKind = theoryPredKind.get(pred);
      if (theoryKind != null) {
        return theoryKind;
      } else {
        return FunctionDeclarationKind.UF;
      }
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
    } else if (input instanceof IEquation) {
      return FunctionDeclarationKind.EQ;
    } else if (input instanceof IIntFormula) {
      IIntFormula f = (IIntFormula) input;
      if (f.rel().equals(IIntRelation.EqZero())) {
        final Sort sort = Sort$.MODULE$.sortOf(((IIntFormula) input).t());
        if (sort == PrincessEnvironment.BOOL_SORT) {
          // this is really a Boolean formula, it has to be UF
          return FunctionDeclarationKind.UF;
        } else if (sort == PrincessEnvironment.INTEGER_SORT) {
          return FunctionDeclarationKind.EQ_ZERO;
        } else {
          return FunctionDeclarationKind.EQ;
        }
      } else if (f.rel().equals(IIntRelation.GeqZero())) {
        return FunctionDeclarationKind.GTE_ZERO;
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
    return (t instanceof IBinFormula) && val.equals(((IBinFormula) t).j()); // j is the operator
  }

  @Override
  public PrincessFunctionDeclaration declareUFImpl(
      String pName, Sort pReturnType, List<Sort> args) {
    return new PrincessIFunctionDeclaration(environment.declareFun(pName, pReturnType, args));
  }

  @Override
  public IExpression callFunctionImpl(
      PrincessFunctionDeclaration declaration, List<IExpression> args) {
    return declaration.makeApp(environment, args);
  }

  @Override
  protected PrincessFunctionDeclaration getBooleanVarDeclarationImpl(IExpression pIExpression) {
    return new PrincessByExampleDeclaration(pIExpression);
  }
}
