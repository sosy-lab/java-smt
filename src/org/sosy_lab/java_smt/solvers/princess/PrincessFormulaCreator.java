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
import static org.sosy_lab.java_smt.solvers.princess.PrincessEnvironment.BOOL_SORT;
import static org.sosy_lab.java_smt.solvers.princess.PrincessEnvironment.INTEGER_SORT;
import static org.sosy_lab.java_smt.solvers.princess.PrincessEnvironment.toSeq;
import static scala.collection.JavaConverters.asJava;
import static scala.collection.JavaConverters.asJavaCollection;

import ap.basetypes.IdealInt;
import ap.parser.ConstantSubstVisitor;
import ap.parser.ExpressionReplacingVisitor;
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
import ap.parser.Rewriter;
import ap.terfor.ConstantTerm;
import ap.terfor.preds.Predicate;
import ap.theories.arrays.ExtArray;
import ap.theories.bitvectors.ModuloArithmetic;
import ap.theories.nia.GroebnerMultiplication;
import ap.theories.nia.GroebnerMultiplication$;
import ap.theories.rationals.Rationals;
import ap.types.Sort;
import ap.types.Sort$;
import ap.types.Sort.MultipleValueBool$;
import com.google.common.base.Preconditions;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import com.google.common.collect.Table;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessBitvectorToBitvectorDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessBitvectorToBooleanDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessByExampleDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessConstArrayDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessEquationDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessIFunctionDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessIntegerDivisionDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessIntegerModuloDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessModularCongruenceDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessMultiplyDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessRationalDivisionDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessRationalFloorDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessRationalMultiplyDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessStringRangeDeclaration;
import scala.Enumeration;
import scala.collection.JavaConverters;

class PrincessFormulaCreator
    extends FormulaCreator<IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  // Hash-maps from interpreted functions and predicates to their corresponding
  // Java-SMT kind
  private static final Map<IFunction, FunctionDeclarationKind> theoryFunctionKind = new HashMap<>();
  private static final Map<Predicate, FunctionDeclarationKind> theoryPredKind = new HashMap<>();

  private static final Set<String> CONSTANT_UFS = ImmutableSet.of("str_cons", "str_empty");

  // Get the symbol for multiplication
  private final IFunction symbolMul = GroebnerMultiplication.mul();

  // We use a list of patterns to match complex operations like division in the visitor
  private final List<Pattern> patterns = precompile();

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
    theoryFunctionKind.put(ModuloArithmetic.bv_smod(), FunctionDeclarationKind.BV_SMOD);
    theoryFunctionKind.put(ModuloArithmetic.bv_shl(), FunctionDeclarationKind.BV_SHL);
    theoryFunctionKind.put(ModuloArithmetic.bv_lshr(), FunctionDeclarationKind.BV_LSHR);
    theoryFunctionKind.put(ModuloArithmetic.bv_ashr(), FunctionDeclarationKind.BV_ASHR);
    theoryFunctionKind.put(ModuloArithmetic.bv_xor(), FunctionDeclarationKind.BV_XOR);
    // modmod.bv_xnor()?
    // modmod.bv_comp()?

    theoryFunctionKind.put(Rationals.addition(), FunctionDeclarationKind.ADD);
    theoryFunctionKind.put(Rationals.multiplication(), FunctionDeclarationKind.MUL);
    theoryFunctionKind.put(Rationals.multWithFraction(), FunctionDeclarationKind.MUL);
    theoryFunctionKind.put(Rationals.multWithRing(), FunctionDeclarationKind.MUL);
    theoryFunctionKind.put(Rationals.division(), FunctionDeclarationKind.DIV);
    theoryFunctionKind.put(Rationals.RatDivZero(), FunctionDeclarationKind.OTHER);

    // casts to integer, sign/zero-extension?

    theoryPredKind.put(ModuloArithmetic.bv_ult(), FunctionDeclarationKind.BV_ULT);
    theoryPredKind.put(ModuloArithmetic.bv_ule(), FunctionDeclarationKind.BV_ULE);
    theoryPredKind.put(ModuloArithmetic.bv_slt(), FunctionDeclarationKind.BV_SLT);
    theoryPredKind.put(ModuloArithmetic.bv_sle(), FunctionDeclarationKind.BV_SLE);
    theoryPredKind.put(Rationals.lessThan(), FunctionDeclarationKind.LT);
    theoryPredKind.put(Rationals.lessThanOrEqual(), FunctionDeclarationKind.LTE);

    theoryFunctionKind.put(GroebnerMultiplication$.MODULE$.mul(), FunctionDeclarationKind.MUL);

    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_$plus$plus(), FunctionDeclarationKind.STR_CONCAT);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_len(), FunctionDeclarationKind.STR_LENGTH);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_indexof(), FunctionDeclarationKind.STR_INDEX_OF);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_at(), FunctionDeclarationKind.STR_CHAR_AT);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_substr(), FunctionDeclarationKind.STR_SUBSTRING);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_replace(), FunctionDeclarationKind.STR_REPLACE);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_replaceall(), FunctionDeclarationKind.STR_REPLACE_ALL);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_to_re(), FunctionDeclarationKind.STR_TO_RE);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_to_int(), FunctionDeclarationKind.STR_TO_INT);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_to_code(), FunctionDeclarationKind.STR_TO_CODE);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_from_code(), FunctionDeclarationKind.STR_FROM_CODE);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_range(), FunctionDeclarationKind.RE_RANGE);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_$plus$plus(), FunctionDeclarationKind.RE_CONCAT);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_union(), FunctionDeclarationKind.RE_UNION);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_inter(), FunctionDeclarationKind.RE_INTERSECT);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_$times(), FunctionDeclarationKind.RE_STAR);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_$plus(), FunctionDeclarationKind.RE_PLUS);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_diff(), FunctionDeclarationKind.RE_DIFFERENCE);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_opt(), FunctionDeclarationKind.RE_OPTIONAL);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_comp(), FunctionDeclarationKind.RE_COMPLEMENT);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.int_to_str(), FunctionDeclarationKind.INT_TO_STR);

    theoryPredKind.put(
        PrincessEnvironment.stringTheory.str_prefixof(), FunctionDeclarationKind.STR_PREFIX);
    theoryPredKind.put(
        PrincessEnvironment.stringTheory.str_suffixof(), FunctionDeclarationKind.STR_SUFFIX);
    theoryPredKind.put(
        PrincessEnvironment.stringTheory.str_contains(), FunctionDeclarationKind.STR_CONTAINS);
    theoryPredKind.put(
        PrincessEnvironment.stringTheory.str_$less$eq(), FunctionDeclarationKind.STR_LE);
    theoryPredKind.put(
        PrincessEnvironment.stringTheory.str_$less(), FunctionDeclarationKind.STR_LT);
    theoryPredKind.put(
        PrincessEnvironment.stringTheory.str_in_re(), FunctionDeclarationKind.STR_IN_RE);
  }

  /**
   * This mapping is a cache from index sort and element sort to the full array sort.
   *
   * <p>This mapping guarantees uniqueness of array types in JavaSMT, i.e. without this cache, we
   * can not compare arrays, because all of them have distinct sorts, and SELECT/STORE operations
   * are also incomparable and result in trivially satisfiable SMT queries (with no visible hint on
   * the reason, except distinct sort objects).
   */
  private final Table<Sort, Sort, Sort> arraySortCache = HashBasedTable.create();

  /** This map keeps track of the bound/free variables created when visiting quantified terms. */
  // TODO should we use a WeakHashMap?
  //  We do not cleanup in other places, too, and the number of quantified formulas is small.
  private final Map<IFormula, String> boundVariableNames = new LinkedHashMap<>();

  PrincessFormulaCreator(PrincessEnvironment pEnv) {
    super(
        pEnv,
        PrincessEnvironment.BOOL_SORT,
        PrincessEnvironment.INTEGER_SORT,
        PrincessEnvironment.FRACTION_SORT,
        PrincessEnvironment.STRING_SORT,
        PrincessEnvironment.REGEX_SORT);
  }

  @Override
  public Object convertValue(IExpression value) {
    if (value instanceof IBoolLit) {
      return ((IBoolLit) value).value();
    } else if (value instanceof IIntLit) {
      return ((IIntLit) value).value().bigIntValue();
    }
    if (value instanceof IFunApp) {
      IFunApp app = (IFunApp) value;
      switch (app.fun().name()) {
        case "true":
          Preconditions.checkArgument(app.fun().arity() == 0);
          return true;
        case "false":
          Preconditions.checkArgument(app.fun().arity() == 0);
          return false;
        case "mod_cast":
          // we found a bitvector BV(lower, upper, ctxt), lets extract the last parameter
          return ((IIntLit) app.apply(2)).value().bigIntValue();
        case "Rat_fromRing":
          Preconditions.checkArgument(app.fun().arity() == 1);
          ITerm term = app.apply(0);
          if (term instanceof IIntLit) {
            return ((IIntLit) term).value().bigIntValue();
          }
          break;
        case "Rat_frac":
          Preconditions.checkArgument(app.fun().arity() == 2);
          ITerm term1 = app.apply(0);
          ITerm term2 = app.apply(1);
          if (term1 instanceof IIntLit && term2 instanceof IIntLit) {
            Rational ratValue =
                Rational.of(
                    ((IIntLit) term1).value().bigIntValue(),
                    ((IIntLit) term2).value().bigIntValue());
            return ratValue.isIntegral() ? ratValue.getNum() : ratValue;
          }
          break;
        case "str_empty":
        case "str_cons":
          return strToString(app);
        default:
      }
    }

    throw new IllegalArgumentException(
        "unhandled model value " + value + " of type " + value.getClass());
  }

  /**
   * convert a recursive string term like "str_cons(97, str_cons(98, str_cons(99, str_empty)))" to a
   * real string "abc" for the user.
   */
  private Object strToString(IFunApp fun) {
    final StringBuilder str = new StringBuilder();
    while ("str_cons".equals(fun.fun().name())) {
      checkArgument(fun.fun().arity() == 2);
      ITerm arg = fun.apply(0);
      IIntLit chr;
      if (arg instanceof IIntLit) {
        chr = ((IIntLit) arg);
      } else if (arg instanceof IFunApp
          && ModuloArithmetic.mod_cast().equals(((IFunApp) arg).fun())) {
        chr = ((IIntLit) ((IFunApp) arg).apply(2));
      } else {
        throw new AssertionError("unexpected string value: " + fun);
      }
      str.append(Character.toString(chr.value().bigIntValue().intValue()));
      fun = (IFunApp) fun.apply(1);
    }
    checkArgument("str_empty".equals(fun.fun().name()));
    checkArgument(fun.fun().arity() == 0);
    return str.toString();
  }

  @Override
  public FormulaType<?> getFormulaType(IExpression pFormula) {
    return PrincessEnvironment.getFormulaType(pFormula);
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
    Sort result = arraySortCache.get(pIndexType, pElementType);
    if (result == null) {
      result = new ExtArray(toSeq(ImmutableList.of(pIndexType)), pElementType).sort();
      arraySortCache.put(pIndexType, pElementType, result);
    }
    return result;
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(final T pFormula) {
    if (pFormula instanceof BitvectorFormula) {
      ITerm input = (ITerm) extractInfo(pFormula);
      Sort sort = Sort$.MODULE$.sortOf(input);
      scala.Option<Object> bitWidth = PrincessEnvironment.getBitWidth(sort);
      checkArgument(
          bitWidth.isDefined(), "BitvectorFormula with actual type %s: %s", sort, pFormula);
      return (FormulaType<T>) FormulaType.getBitvectorTypeWithSize((Integer) bitWidth.get());

    } else if (pFormula instanceof ArrayFormula<?, ?>) {
      final FormulaType<?> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<?, ?>) pFormula);
      final FormulaType<?> arrayElementType =
          getArrayFormulaElementType((ArrayFormula<?, ?>) pFormula);
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    }

    return super.getFormulaType(pFormula);
  }

  private String getName(IExpression input) {
    if (input instanceof IAtom) {
      return ((IAtom) input).pred().name();
    } else if (input instanceof IConstant) {
      return ((IConstant) input).c().name();
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

  /** Returns true if the expression is a constant value. */
  private static boolean isValue(IExpression input) {
    if (input instanceof IBoolLit || input instanceof IIntLit) {
      // Boolean or integer literal
      return true;
    } else if (input instanceof IFunApp) {
      IFunApp app = (IFunApp) input;
      IFunction fun = app.fun();
      if (fun.equals(Rationals.fromRing()) || fun.equals(Rationals.frac())) {
        // Rational number literal
        for (IExpression sub : asJava(app.args())) {
          if (!(sub instanceof IIntLit)) {
            return false;
          }
        }
        return true;
      }
      if (fun.equals(ModuloArithmetic.mod_cast()) && input.apply(2) instanceof IIntLit) {
        // Bitvector literal
        return true;
      }
      if (CONSTANT_UFS.contains(fun.name())) {
        // Nil, Cons from String theory
        return true;
      }
    }
    return false;
  }

  /** Cast integer terms to rational, if needed. */
  private ITerm toReal(ITerm number) {
    return getFormulaType(number).isIntegerType() ? Rationals.int2ring(number) : number;
  }

  private static class Pair<A, B> {
    private final A a;
    private final B b;

    Pair(A pA, B pB) {
      a = pA;
      b = pB;
    }

    A getA() {
      return a;
    }

    B getB() {
      return b;
    }
  }

  /** Merge two substitutions, returns {@link Optional#empty()} when there is a conflict. */
  private <A, B> Optional<Map<A, B>> merge(
      Optional<Map<A, B>> maybeSubst1, Optional<Map<A, B>> maybeSubst2) {
    if (maybeSubst1.isPresent() && maybeSubst2.isPresent()) {
      var subst1 = maybeSubst1.orElseThrow();
      var subst2 = maybeSubst2.orElseThrow();

      ImmutableMap.Builder<A, B> builder = ImmutableMap.builder();
      for (var k : Sets.union(subst1.keySet(), subst2.keySet())) {
        if (subst1.containsKey(k)) {
          if (subst2.containsKey(k) && !subst1.get(k).equals(subst2.get(k))) {
            return Optional.empty();
          }
          builder.put(k, subst1.get(k));
        } else {
          builder.put(k, subst2.get(k));
        }
      }
      return Optional.of(builder.buildOrThrow());
    } else {
      return Optional.empty();
    }
  }

  /**
   * Simple term unification.
   *
   * <p>Assumes that the left term is more general. Will return {@link Optional#empty()} if the
   * terms can't be unified. Otherwise, returns a substitution for the constant symbols in the left
   * term.
   */
  private Pair<Optional<Map<ConstantTerm, IExpression>>, IExpression> unify(
      IExpression t1, IExpression t2) {
    if (t1.equals(t2)) {
      return new Pair<>(Optional.of(ImmutableMap.of()), t1);
    } else if (t1 instanceof IConstant) {
      return new Pair<>(Optional.of(ImmutableMap.of(((IConstant) t1).c(), t2)), t2);
    } else if (t1.getClass().equals(t2.getClass()) && t1.length() == t2.length()) {
      // Recursively check the subterms
      Optional<Map<ConstantTerm, IExpression>> subst = Optional.of(ImmutableMap.of());
      ImmutableList.Builder<IExpression> terms = ImmutableList.builder();
      for (var i = 0; i < t1.length(); i++) {
        Pair<Optional<Map<ConstantTerm, IExpression>>, IExpression> r =
            unify(t1.apply(i), t2.apply(i));
        subst = merge(subst, r.getA());

        if (subst.isEmpty()) {
          return new Pair<>(Optional.empty(), t1);
        }
        terms.add(r.getB());
      }

      // Check if the left term is equal to the right after the subtrees were unified
      IExpression t = t1.update(toSeq(terms.build()));
      if (t.equals(t2)) {
        return new Pair<>(subst, t2);
      }
    }
    return new Pair<>(Optional.empty(), t1);
  }

  /**
   * Rewrite terms of the form <code>((_ ITimes k) b)</code> as <code>(multiply (Expression.i k) b)
   * </code>.
   *
   * <p>This will later allow us to replace the first argument with a variable
   */
  private IExpression rewriteMult(IExpression t) {
    return Rewriter.rewrite(
        t,
        v -> {
          if (v instanceof ITimes) {
            var times = (ITimes) v;
            return new IFunApp(
                symbolMul, toSeq(ImmutableList.of(IExpression.i(times.coeff()), times.subterm())));
          } else {
            return v;
          }
        });
  }

  /**
   * Rewrite negative integer literals as <code>-1 * a</code>.
   *
   * <p>Will skip <code>-1</code> terms while rewriting
   */
  private IExpression rewriteNegated(IExpression t) {
    return Rewriter.rewrite(
        t,
        v -> {
          if (v instanceof IIntLit) {
            var lit = ((IIntLit) v);
            if (!lit.value().isUnit() && lit.value().signum() < 0) {
              return new ITimes(IdealInt.apply(-1), IExpression.abs(lit));
            }
          }
          return v;
        });
  }

  /**
   * A pattern, consisting of an operation, it's arguments, and the resulting Princess term.
   *
   * <p>The princess term will be generalized, and by matching it to a given formula one can invert
   * the operation and derive the original arguments.
   */
  private static class Pattern {
    private final PrincessFunctionDeclaration decl;
    private final List<IExpression> args;
    private final IExpression term;

    Pattern(PrincessFunctionDeclaration pDecl, List<IExpression> pArgs, IExpression pTerm) {
      decl = pDecl;
      args = pArgs;
      term = pTerm;
    }
  }

  private Pattern buildPattern(PrincessFunctionDeclaration pDeclaration, List<IExpression> pArgs) {
    return buildPattern(pDeclaration, pArgs, false);
  }

  /**
   * Helper function to build patterns.
   *
   * <p>If the last argument is set to <code>true</code>, we will generalize any constant terms in
   * the arguments.
   */
  private Pattern buildPattern(
      PrincessFunctionDeclaration pDeclaration, List<IExpression> pArgs, boolean pFinal) {
    var term = rewriteNegated(rewriteMult(pDeclaration.makeApp(environment, pArgs)));
    if (pFinal) {
      ImmutableList.Builder<IExpression> builder = ImmutableList.builder();
      for (var c : pArgs) {
        if (c instanceof IConstant) {
          // If the argument is already a variable, just keep it
          builder.add(c);
        } else if (c instanceof ITimes) {
          // If it's a term (c * t), where c is an integer coefficient, and t is another integer
          // literal, we replace t in (c * t) with a new variable
          // Specifically, this can be used to generalize negative integer constants by first
          // shifting the minus sign outside, and then replacing the nested integer term
          var times = (ITimes) c;
          if (times.apply(0) instanceof IIntLit) {
            var newVar =
                (ITerm) makeVariable(INTEGER_SORT, "@" + Integer.toUnsignedString(c.hashCode()));
            term = ExpressionReplacingVisitor.apply(term, times.apply(0), newVar);
            builder.add(new ITimes(times.coeff(), newVar));
          } else {
            throw new IllegalArgumentException();
          }
        } else {
          // If we have an integer constant as argument, replace it with a new variable and
          // update the term
          var newVar =
              (ITerm) makeVariable(INTEGER_SORT, "@" + Integer.toUnsignedString(c.hashCode()));
          term = ExpressionReplacingVisitor.apply(term, c, newVar);
          builder.add(newVar);
        }
      }
      return new Pattern(pDeclaration, builder.build(), term);
    } else {
      return new Pattern(pDeclaration, pArgs, term);
    }
  }

  private List<Pattern> precompile() {
    // Define two variable to match integer arguments
    ITerm symbolInt1 = (ITerm) makeVariable(PrincessEnvironment.INTEGER_SORT, "@1integer");
    ITerm symbolInt2 = (ITerm) makeVariable(PrincessEnvironment.INTEGER_SORT, "@2integer");

    // Define two variables for real arguments
    ITerm symbolReal1 = (ITerm) makeVariable(PrincessEnvironment.FRACTION_SORT, "@1real");
    ITerm symbolReal2 = (ITerm) makeVariable(PrincessEnvironment.FRACTION_SORT, "@2real");

    return ImmutableList.of(
        // Rational.divide
        buildPattern(
            PrincessRationalDivisionDeclaration.INSTANCE,
            ImmutableList.of(symbolReal1, toReal(symbolInt2)),
            true),
        buildPattern(
            PrincessRationalDivisionDeclaration.INSTANCE,
            ImmutableList.of(symbolReal1, symbolReal2)),

        // Rational.floor
        buildPattern(PrincessRationalFloorDeclaration.INSTANCE, ImmutableList.of(symbolReal1)),

        // Integer.divide
        buildPattern(
            PrincessIntegerDivisionDeclaration.INSTANCE,
            ImmutableList.of(IExpression.i(2), symbolInt2),
            true),
        buildPattern(
            PrincessIntegerDivisionDeclaration.INSTANCE,
            ImmutableList.of(symbolInt1, IExpression.i(2))),
        buildPattern(
            PrincessIntegerDivisionDeclaration.INSTANCE,
            ImmutableList.of(symbolInt1, IExpression.i(2).unary_$minus())),
        buildPattern(
            PrincessIntegerDivisionDeclaration.INSTANCE,
            ImmutableList.of(symbolInt1, IExpression.i(3)),
            true),
        buildPattern(
            PrincessIntegerDivisionDeclaration.INSTANCE,
            ImmutableList.of(symbolInt1, IExpression.i(3).unary_$minus()),
            true),

        // Integer.modulo
        buildPattern(
            PrincessIntegerModuloDeclaration.INSTANCE, ImmutableList.of(symbolInt1, symbolInt2)),
        buildPattern(
            PrincessIntegerModuloDeclaration.INSTANCE,
            ImmutableList.of(symbolInt1, IExpression.i(2))),
        buildPattern(
            PrincessIntegerModuloDeclaration.INSTANCE,
            ImmutableList.of(symbolInt1, IExpression.i(2).unary_$minus()),
            true),
        buildPattern(
            PrincessIntegerModuloDeclaration.INSTANCE,
            ImmutableList.of(symbolInt1, IExpression.i(3)),
            true),
        buildPattern(
            PrincessIntegerModuloDeclaration.INSTANCE,
            ImmutableList.of(symbolInt1, IExpression.i(3).unary_$minus()),
            true),

        // Integer.modularCongruence
        buildPattern(
            PrincessModularCongruenceDeclaration.INSTANCE,
            ImmutableList.of(symbolInt1, symbolInt2, IExpression.i(3)),
            true),

        // String.range
        buildPattern(
            PrincessStringRangeDeclaration.INSTANCE,
            ImmutableList.of(
                makeVariable(getStringType(), "@1Str"), makeVariable(getStringType(), "@2Str")),
            false));
  }

  @SuppressWarnings("deprecation")
  @Override
  public <R> R visit(FormulaVisitor<R> visitor, final Formula f, final IExpression input) {
    IExpression re = rewriteNegated(rewriteMult(input));

    // Check if one of the patterns matches
    for (Pattern p : patterns) {
      Optional<Map<ConstantTerm, IExpression>> subst = unify(p.term, re).getA();

      if (subst.isPresent()) {
        ImmutableList.Builder<Formula> args = ImmutableList.builder();
        ImmutableList.Builder<FormulaType<?>> sorts = ImmutableList.builder();

        for (IExpression arg : p.args) {
          ImmutableMap.Builder<ConstantTerm, ITerm> builder = ImmutableMap.builder();
          for (var entry : subst.orElseThrow().entrySet()) {
            builder.put(entry.getKey(), (ITerm) entry.getValue());
          }
          IExpression updated =
              ConstantSubstVisitor.apply(arg, JavaConverters.asScala(builder.buildOrThrow()));
          updated =
              Rewriter.rewrite(
                  updated,
                  v -> {
                    if (v instanceof ITimes) {
                      var times = (ITimes) v;
                      if (times.apply(0) instanceof IIntLit) {
                        var lit = (IIntLit) times.apply(0);
                        return IExpression.i(times.coeff().$times(lit.value()));
                      }
                    }
                    return v;
                  });

          args.add(encapsulateWithTypeOf(updated));
          sorts.add(getFormulaType(updated));
        }

        return visitor.visitFunction(
            f,
            args.build(),
            FunctionDeclarationImpl.of(
                p.decl.getName(), p.decl.getKind(), sorts.build(), getFormulaType(f), p.decl));
      }
    }

    if (isValue(input)) {
      return visitor.visitConstant(encapsulateWithTypeOf(input), convertValue(input));
    }
    if (input instanceof IQuantified) {
      // Is it a quantifier?
      return visitQuantifier(visitor, (BooleanFormula) f, (IQuantified) input);

    } else if (((input instanceof IAtom) && asJavaCollection(((IAtom) input).args()).isEmpty())
        || input instanceof IConstant) {
      // nullary atoms and constant are variables
      return visitor.visitFreeVariable(f, input.toString());

    } else if (input instanceof ITimes) {
      // Princess encodes nonlinear multiplication as (coefficient* t), where "coefficient" is
      // an integer constant and "t" is the only subterm
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
    }

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
    }

    if (kind == FunctionDeclarationKind.UF && input instanceof IIntFormula) {
      assert ((IIntFormula) input).rel().equals(IIntRelation.EqZero());
      // this is really a Boolean formula, visit the lhs of the equation
      return visit(visitor, f, ((IIntFormula) input).t());
    }

    ImmutableList.Builder<Formula> args = ImmutableList.builder();
    ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();
    int arity = input.length();
    int arityStart = 0;

    PrincessFunctionDeclaration solverDeclaration;
    if (isBitvectorOperationWithAdditionalArgument(kind)) {
      // the first argument is the bitsize, and it is not relevant for the user.
      // we do not want type/sort information as arguments.
      arityStart = 1;
      if (input instanceof IAtom) {
        solverDeclaration = new PrincessBitvectorToBooleanDeclaration(((IAtom) input).pred());
      } else if (input instanceof IFunApp) {
        solverDeclaration = new PrincessBitvectorToBitvectorDeclaration(((IFunApp) input).fun());
      } else {
        throw new AssertionError(
            String.format("unexpected bitvector operation '%s' for formula '%s'", kind, input));
      }
    } else if (input instanceof IFunApp) {
      if (kind == FunctionDeclarationKind.UF) {
        solverDeclaration = new PrincessIFunctionDeclaration(((IFunApp) input).fun());
      } else if (kind == FunctionDeclarationKind.MUL) {
        if (getFormulaType(input.apply(0)).isRationalType()) {
          solverDeclaration = PrincessRationalMultiplyDeclaration.INSTANCE;
        } else if (getFormulaType(input.apply(0)).isIntegerType()) {
          solverDeclaration = PrincessMultiplyDeclaration.INSTANCE;
        } else {
          throw new IllegalArgumentException();
        }
      } else if (kind == FunctionDeclarationKind.CONST) {
        solverDeclaration = new PrincessConstArrayDeclaration(environment, (IFunApp) input);
      } else {
        solverDeclaration = new PrincessByExampleDeclaration(input);
      }
    } else {
      solverDeclaration = new PrincessByExampleDeclaration(input);
    }

    for (int i = arityStart; i < arity; i++) {
      IExpression arg = input.apply(i);
      FormulaType<?> argumentType = getFormulaType(arg);
      args.add(encapsulate(argumentType, arg));
      argTypes.add(argumentType);
    }

    return visitor.visitFunction(
        f,
        args.build(),
        FunctionDeclarationImpl.of(
            getName(input), kind, argTypes.build(), getFormulaType(f), solverDeclaration));
  }

  private <R> R visitQuantifier(FormulaVisitor<R> visitor, BooleanFormula f, IQuantified input) {
    Quantifier quantifier =
        input.quan().equals(ap.terfor.conjunctions.Quantifier.apply(true)) ? FORALL : EXISTS;
    IFormula body = input.subformula();

    // Princess uses de-Bruijn indices, so we have index 0 here for the most outer quantified scope
    IVariable boundVariable = input.sort().boundVariable(0);
    String boundVariableName = getFreshVariableNameForBody(body);

    // Currently, Princess supports only non-boolean bound variables, so we can cast to ITerm.
    ITerm substitutionVariable = (ITerm) makeVariable(boundVariable.sort(), boundVariableName);

    // substitute the bound variable with index 0 with a new variable, and un-shift the remaining
    // de-Bruijn indices, such that the next nested bound variable has index 0.
    IFormula substitutedBody = IExpression.subst(body, asScalaList(substitutionVariable), -1);

    return visitor.visitQuantifier(
        f,
        quantifier,
        ImmutableList.of(encapsulateWithTypeOf(substitutionVariable)),
        encapsulateBoolean(substitutedBody));
  }

  private static scala.collection.immutable.List<ITerm> asScalaList(ITerm substitutionVariable) {
    return scala.collection.immutable.List$.MODULE$.empty().$colon$colon(substitutionVariable);
  }

  /**
   * Get a fresh variable name for the given formula. We compute the same variable name for the same
   * body, such that a user gets the same substituted body when visiting a quantified formulas
   * several times.
   */
  private String getFreshVariableNameForBody(IFormula body) {
    return boundVariableNames.computeIfAbsent(
        body, k -> "__JAVASMT__BOUND_VARIABLE_" + boundVariableNames.size());
  }

  private boolean isBitvectorOperationWithAdditionalArgument(FunctionDeclarationKind kind) {
    switch (kind) {
      case BV_NOT:
      case BV_NEG:
      case BV_OR:
      case BV_AND:
      case BV_XOR:
      case BV_SUB:
      case BV_ADD:
      case BV_SDIV:
      case BV_UDIV:
      case BV_SREM:
      case BV_UREM:
      case BV_SMOD:
      case BV_MUL:
      case BV_ULT:
      case BV_SLT:
      case BV_ULE:
      case BV_SLE:
      case BV_UGT:
      case BV_SGT:
      case BV_UGE:
      case BV_SGE:
      case BV_EQ:
        return true;
      default:
        return false;
    }
  }

  private FunctionDeclarationKind getDeclarationKind(IExpression input) {
    assert !(((input instanceof IAtom) && asJavaCollection(((IAtom) input).args()).isEmpty())
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
      } else if (ExtArray.Const$.MODULE$.unapply(fun).isDefined()) {
        return FunctionDeclarationKind.CONST;
      } else if (fun == ModuloArithmetic.mod_cast()) {
        return FunctionDeclarationKind.OTHER;
      } else if (((IFunApp) input).fun().equals(Rationals.fromRing())) {
        return FunctionDeclarationKind.TO_REAL;
      } else {
        return FunctionDeclarationKind.UF;
      }
    } else if (input instanceof IAtom) {
      final Predicate pred = ((IAtom) input).pred();
      return theoryPredKind.getOrDefault(pred, FunctionDeclarationKind.UF);
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
        if (sort == Sort.MultipleValueBool$.MODULE$) {
          // Princess does not allow UFs to have return sort 'Bool'
          // Instead, the function returns 'MultiplyValueBool' which is really an integer. The
          // predicate (=0 (uf ...)) is then wrapped around the function application to get a
          // (boolean) formula
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
      // they are either handled implicitly by the above-mentioned parts or not at all
      return FunctionDeclarationKind.OTHER;
    }
  }

  private static boolean isBinaryFunction(IExpression t, Enumeration.Value val) {
    return (t instanceof IBinFormula) && val.equals(((IBinFormula) t).j()); // j is the operator
  }

  @Override
  public PrincessFunctionDeclaration declareUFImpl(
      String pName, Sort pReturnType, List<Sort> args) {
    return new PrincessIFunctionDeclaration(
        environment.declareFun(
            pName, pReturnType.equals(BOOL_SORT) ? MultipleValueBool$.MODULE$ : pReturnType, args));
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
