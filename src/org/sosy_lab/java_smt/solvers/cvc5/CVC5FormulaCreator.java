// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Pair;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.cvc5.CVC5Formula.CVC5ArrayFormula;
import org.sosy_lab.java_smt.solvers.cvc5.CVC5Formula.CVC5BitvectorFormula;
import org.sosy_lab.java_smt.solvers.cvc5.CVC5Formula.CVC5BooleanFormula;
import org.sosy_lab.java_smt.solvers.cvc5.CVC5Formula.CVC5FloatingPointFormula;
import org.sosy_lab.java_smt.solvers.cvc5.CVC5Formula.CVC5FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.solvers.cvc5.CVC5Formula.CVC5IntegerFormula;
import org.sosy_lab.java_smt.solvers.cvc5.CVC5Formula.CVC5RationalFormula;
import org.sosy_lab.java_smt.solvers.cvc5.CVC5Formula.CVC5RegexFormula;
import org.sosy_lab.java_smt.solvers.cvc5.CVC5Formula.CVC5StringFormula;

public class CVC5FormulaCreator extends FormulaCreator<Term, Sort, Solver, Term> {

  // private static final Pattern FLOATING_POINT_PATTERN = Pattern.compile("^\\(fp #b(?<sign>\\d)
  // #b(?<exp>\\d+) #b(?<mant>\\d+)$");

  private final Map<String, Term> variablesCache = new HashMap<>();
  private final Map<String, Term> functionsCache = new HashMap<>();
  private final Solver solver;

  protected CVC5FormulaCreator(Solver pSolver) {
    super(
        pSolver,
        pSolver.getBooleanSort(),
        pSolver.getIntegerSort(),
        pSolver.getRealSort(),
        pSolver.getStringSort(),
        pSolver.getRegExpSort());
    solver = pSolver;
  }

  @Override
  public Term makeVariable(Sort sort, String name) {
    Term exp = variablesCache.computeIfAbsent(name, n -> solver.mkConst(sort, name));
    Preconditions.checkArgument(
        sort.equals(exp.getSort()),
        "symbol name already in use for different Type %s",
        exp.getSort());
    return exp;
  }

  /**
   * Makes a bound copy of a variable for use in quantifier. Note that all occurrences of the free
   * var have to be substituted by the bound once it exists.
   *
   * @param var Variable you want a bound copy of.
   * @return Bound Variable
   */
  public Term makeBoundCopy(Term var) {
    Sort sort = var.getSort();
    String name = getName(var);
    Term boundCopy = solver.mkVar(sort, name);
    return boundCopy;
  }

  @Override
  public Sort getBitvectorType(int pBitwidth) {
    try {
      return solver.mkBitVectorSort(pBitwidth);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid bitvector sort with size " + pBitwidth + ".", e);
    }
  }

  @Override
  public Sort getFloatingPointType(FloatingPointType pType) {
    try {
      // plus sign bit
      return solver.mkFloatingPointSort(pType.getExponentSize(), pType.getMantissaSize() + 1);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid floatingpoint sort with exponent size "
              + pType.getExponentSize()
              + " and mantissa "
              + pType.getMantissaSize()
              + ".",
          e);
    }
  }

  @Override
  public Sort getArrayType(Sort pIndexType, Sort pElementType) {
    return solver.mkArraySort(pIndexType, pElementType);
  }

  @Override
  public Term extractInfo(Formula pT) {
    return CVC5FormulaManager.getCVC5Term(pT);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TD extends Formula, TR extends Formula> FormulaType<TR> getArrayFormulaElementType(
      ArrayFormula<TD, TR> pArray) {
    return ((CVC5ArrayFormula<TD, TR>) pArray).getElementType();
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TD extends Formula, TR extends Formula> FormulaType<TD> getArrayFormulaIndexType(
      ArrayFormula<TD, TR> pArray) {
    return ((CVC5ArrayFormula<TD, TR>) pArray).getIndexType();
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    Sort cvc5sort = extractInfo(pFormula).getSort();
    if (pFormula instanceof BitvectorFormula) {
      checkArgument(
          cvc5sort.isBitVector(), "BitvectorFormula with actual Type %s: %s", cvc5sort, pFormula);
      return (FormulaType<T>) getFormulaType(extractInfo(pFormula));

    } else if (pFormula instanceof FloatingPointFormula) {
      checkArgument(
          cvc5sort.isFloatingPoint(),
          "FloatingPointFormula with actual Type %s: %s",
          cvc5sort,
          pFormula);
      return (FormulaType<T>)
          FormulaType.getFloatingPointType(
              cvc5sort.getFloatingPointExponentSize(),
              cvc5sort.getFloatingPointSignificandSize() - 1); // TODO: check for sign bit

    } else if (pFormula instanceof ArrayFormula<?, ?>) {
      FormulaType<T> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<T, T>) pFormula);
      FormulaType<T> arrayElementType = getArrayFormulaElementType((ArrayFormula<T, T>) pFormula);
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    }
    return super.getFormulaType(pFormula);
  }

  @Override
  public FormulaType<?> getFormulaType(Term pFormula) {
    return getFormulaTypeFromTermType(pFormula.getSort());
  }

  private FormulaType<?> getFormulaTypeFromTermType(Sort sort) {
    if (sort.isBoolean()) {
      return FormulaType.BooleanType;
    } else if (sort.isInteger()) {
      return FormulaType.IntegerType;
    } else if (sort.isBitVector()) {
      return FormulaType.getBitvectorTypeWithSize(sort.getBitVectorSize());
    } else if (sort.isFloatingPoint()) {
      // CVC5 wants the sign bit as part of the mantissa. We add that manually in creation.
      return FormulaType.getFloatingPointType(
          sort.getFloatingPointExponentSize(), sort.getFloatingPointSignificandSize() - 1);
    } else if (sort.isRoundingMode()) {
      return FormulaType.FloatingPointRoundingModeType;
    } else if (sort.isReal()) {
      // The theory REAL in CVC5 is the theory of (infinite precision!) real numbers.
      // As such, the theory RATIONAL is contained in REAL. TODO: find a better solution.
      return FormulaType.RationalType;
    } else if (sort.isArray()) {
      FormulaType<?> indexType = getFormulaTypeFromTermType(sort.getArrayIndexSort());
      FormulaType<?> elementType = getFormulaTypeFromTermType(sort.getArrayElementSort());
      return FormulaType.getArrayType(indexType, elementType);
    } else if (sort.isString()) {
      return FormulaType.StringType;
    } else if (sort.isRegExp()) {
      return FormulaType.RegexType;
    } else if (sort.isFunction()) {
      return getFormulaTypeFromTermType(sort.getFunctionCodomainSort());
    } else {
      throw new AssertionError(String.format("Encountered unhandled Type '%s'.", sort));
    }
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, Term pTerm) {
    assert pType.equals(getFormulaType(pTerm))
            || (pType.equals(FormulaType.RationalType)
                && getFormulaType(pTerm).equals(FormulaType.IntegerType))
        : String.format(
            "Trying to encapsulate formula %s of Type %s as %s",
            pTerm, getFormulaType(pTerm), pType);
    if (pType.isBooleanType()) {
      return (T) new CVC5BooleanFormula(pTerm);
    } else if (pType.isIntegerType()) {
      return (T) new CVC5IntegerFormula(pTerm);
    } else if (pType.isRationalType()) {
      return (T) new CVC5RationalFormula(pTerm);
    } else if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrFt = (ArrayFormulaType<?, ?>) pType;
      return (T) new CVC5ArrayFormula<>(pTerm, arrFt.getIndexType(), arrFt.getElementType());
    } else if (pType.isBitvectorType()) {
      return (T) new CVC5BitvectorFormula(pTerm);
    } else if (pType.isFloatingPointType()) {
      return (T) new CVC5FloatingPointFormula(pTerm);
    } else if (pType.isFloatingPointRoundingModeType()) {
      return (T) new CVC5FloatingPointRoundingModeFormula(pTerm);
    } else if (pType.isStringType()) {
      return (T) new CVC5StringFormula(pTerm);
    } else if (pType.isRegexType()) {
      return (T) new CVC5RegexFormula(pTerm);
    }
    throw new IllegalArgumentException("Cannot create formulas of Type " + pType + " in CVC5");
  }

  private Formula encapsulate(Term pTerm) {
    return encapsulate(getFormulaType(pTerm), pTerm);
  }

  @Override
  public BooleanFormula encapsulateBoolean(Term pTerm) {
    assert getFormulaType(pTerm).isBooleanType()
        : String.format(
            "%s is not boolean, but %s (%s)", pTerm, pTerm.getSort(), getFormulaType(pTerm));
    return new CVC5BooleanFormula(pTerm);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Term pTerm) {
    assert getFormulaType(pTerm).isBitvectorType()
        : String.format("%s is no BV, but %s (%s)", pTerm, pTerm.getSort(), getFormulaType(pTerm));
    return new CVC5BitvectorFormula(pTerm);
  }

  @Override
  protected FloatingPointFormula encapsulateFloatingPoint(Term pTerm) {
    assert getFormulaType(pTerm).isFloatingPointType()
        : String.format("%s is no FP, but %s (%s)", pTerm, pTerm.getSort(), getFormulaType(pTerm));
    return new CVC5FloatingPointFormula(pTerm);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      Term pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType))
        : String.format(
            "%s is no array, but %s (%s)", pTerm, pTerm.getSort(), getFormulaType(pTerm));
    return new CVC5ArrayFormula<>(pTerm, pIndexType, pElementType);
  }

  @Override
  protected StringFormula encapsulateString(Term pTerm) {
    assert getFormulaType(pTerm).isStringType()
        : String.format(
            "%s is no String, but %s (%s)", pTerm, pTerm.getSort(), getFormulaType(pTerm));
    return new CVC5StringFormula(pTerm);
  }

  @Override
  protected RegexFormula encapsulateRegex(Term pTerm) {
    assert getFormulaType(pTerm).isRegexType();
    return new CVC5RegexFormula(pTerm);
  }

  private String getName(Term e) {
    checkState(!e.isNull());
    try {
      if (e.getKind() == Kind.APPLY_UF) {
        e = e.getChild(0);
      }
    } catch (CVC5ApiException e1) {
      // Fallback is the String of the original term
    }
    return dequote(e.toString());
  }

  private String getFunctionName(Term e) {
    try {
      if (e.getKind() == Kind.APPLY_UF) {
        e = e.getChild(0);
      }
    } catch (CVC5ApiException e1) {
      // Fallback is the String of the original term
    }
    // Functions are packaged like this: (functionName arg1 arg2 ...)
    return dequote(e.toString()).replace("(", "").split(" ")[0];
  }

  /** Variable names can be wrapped with "|". This function removes those chars. */
  private static String dequote(String s) {
    int l = s.length();
    if (s.charAt(0) == '|' && s.charAt(l - 1) == '|') {
      return s.substring(1, l - 1);
    }
    return s;
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, final Term f) {
    checkState(!f.isNull());
    Sort sort = f.getSort();
    try {
      if (f.isBooleanValue()) {
        return visitor.visitConstant(formula, f.getBooleanValue());

      } else if (f.isStringValue()) {
        return visitor.visitConstant(formula, f.getStringValue());

      } else if (f.isRealValue()) {
        Pair<BigInteger, BigInteger> realValue = f.getRealValue();
        return visitor.visitConstant(formula, Rational.of(realValue.first, realValue.second));

      } else if (f.isIntegerValue()) {
        return visitor.visitConstant(formula, f.getIntegerValue());

      } else if (f.isBitVectorValue()) {
        return visitor.visitConstant(formula, f.getBitVectorValue());

      } else if (f.isFloatingPointValue()) {
        // String is easier to parse here
        return visitor.visitConstant(formula, f.toString());

      } else if (f.getKind() == Kind.CONST_ROUNDINGMODE) {
        return visitor.visitConstant(formula, f.toString());

      } else if (f.getKind() == Kind.VARIABLE) {
        // BOUND vars are used for all vars that are bound to a quantifier in CVC5.
        // We resubstitute them back to the original free.
        // CVC5 doesn't give you the de-brujin index
        Term originalVar = variablesCache.get(dequote(formula.toString()));
        return visitor.visitBoundVariable(encapsulate(originalVar), 0);

      } else if (f.getKind() == Kind.FORALL || f.getKind() == Kind.EXISTS) {
        // QUANTIFIER: replace bound variable with free variable for visitation
        assert f.getNumChildren() == 2;
        Term body = f.getChild(1);
        List<Formula> freeVars = new ArrayList<>();
        for (Term boundVar : f.getChild(0)) { // unpack grand-children of f.
          String name = getName(boundVar);
          Term freeVar = Preconditions.checkNotNull(variablesCache.get(name));
          body = body.substitute(boundVar, freeVar);
          freeVars.add(encapsulate(freeVar));
        }
        BooleanFormula fBody = encapsulateBoolean(body);
        Quantifier quant = f.getKind() == Kind.EXISTS ? Quantifier.EXISTS : Quantifier.FORALL;
        return visitor.visitQuantifier((BooleanFormula) formula, quant, freeVars, fBody);

      } else if (f.getKind() == Kind.CONSTANT) {
        return visitor.visitFreeVariable(formula, dequote(f.toString()));

      } else {
        // Term expressions like uninterpreted function calls (Kind.APPLY_UF) or operators (e.g.
        // Kind.AND).
        // These are all treated like operators, so we can get the declaration by f.getOperator()!

        ImmutableList.Builder<Formula> argsBuilder = ImmutableList.builder();

        List<FormulaType<?>> argsTypes = new ArrayList<>();

        // Term operator = normalize(f.getSort());
        Kind kind = f.getKind();
        if (sort.isFunction() || kind == Kind.APPLY_UF) {
          // The arguments are all children except the first one
          for (int i = 1; i < f.getNumChildren(); i++) {
            argsTypes.add(getFormulaTypeFromTermType(f.getChild(i).getSort()));
            // CVC5s first argument in a function/Uf is the declaration, we don't need that here
            argsBuilder.add(encapsulate(f.getChild(i)));
          }
        } else {
          for (Term arg : f) {
            argsTypes.add(getFormulaType(arg));
            argsBuilder.add(encapsulate(arg));
          }
        }

        // TODO some operations (BV_SIGN_EXTEND, BV_ZERO_EXTEND, maybe more) encode information as
        // part of the operator itself, thus the arity is one too small and there might be no
        // possibility to access the information from user side. Should we encode such information
        // as additional parameters? We do so for some methods of Princess.
        if (sort.isFunction()) {
          return visitor.visitFunction(
              formula,
              argsBuilder.build(),
              FunctionDeclarationImpl.of(
                  getFunctionName(f), getDeclarationKind(f), argsTypes, getFormulaType(f), f));
        } else if (kind == Kind.APPLY_UF) {
          return visitor.visitFunction(
              formula,
              argsBuilder.build(),
              FunctionDeclarationImpl.of(
                  getFunctionName(f),
                  getDeclarationKind(f),
                  argsTypes,
                  getFormulaType(f),
                  normalize(f.getChild(0))));
        } else {
          // TODO: check if the below is correct
          return visitor.visitFunction(
              formula,
              argsBuilder.build(),
              FunctionDeclarationImpl.of(
                  getFunctionName(f),
                  getDeclarationKind(f),
                  argsTypes,
                  getFormulaType(f),
                  f.getOp()));
        }
      }
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "Failure visiting the Term " + f + ". " + e.getMessage(), e);
    }
  }

  /**
   * CVC5 returns new objects when querying operators for UFs. The new operator has to be translated
   * back to a common one.
   */
  private Term normalize(Term operator) {
    Term function = functionsCache.get(getName(operator));
    if (function != null) {
      checkState(
          function.getId() == operator.getId(),
          "operator '%s' with ID %s differs from existing function '%s' with ID '%s'.",
          operator,
          operator.getId(),
          function,
          function.getId());
      return function;
    }
    return operator;
  }

  // see src/theory/*/kinds in CVC5 sources for description of the different CVC5 kinds ;)
  private static final ImmutableMap<Kind, FunctionDeclarationKind> KIND_MAPPING =
      ImmutableMap.<Kind, FunctionDeclarationKind>builder()
          .put(Kind.EQUAL, FunctionDeclarationKind.EQ)
          .put(Kind.DISTINCT, FunctionDeclarationKind.DISTINCT)
          .put(Kind.NOT, FunctionDeclarationKind.NOT)
          .put(Kind.AND, FunctionDeclarationKind.AND)
          .put(Kind.IMPLIES, FunctionDeclarationKind.IMPLIES)
          .put(Kind.OR, FunctionDeclarationKind.OR)
          .put(Kind.XOR, FunctionDeclarationKind.XOR)
          .put(Kind.ITE, FunctionDeclarationKind.ITE)
          .put(Kind.APPLY_UF, FunctionDeclarationKind.UF)
          .put(Kind.ADD, FunctionDeclarationKind.ADD)
          .put(Kind.MULT, FunctionDeclarationKind.MUL)
          .put(Kind.SUB, FunctionDeclarationKind.SUB)
          .put(Kind.DIVISION, FunctionDeclarationKind.DIV)
          .put(Kind.LT, FunctionDeclarationKind.LT)
          .put(Kind.LEQ, FunctionDeclarationKind.LTE)
          .put(Kind.GT, FunctionDeclarationKind.GT)
          .put(Kind.GEQ, FunctionDeclarationKind.GTE)
          // Bitvector theory
          .put(Kind.BITVECTOR_ADD, FunctionDeclarationKind.BV_ADD)
          .put(Kind.BITVECTOR_SUB, FunctionDeclarationKind.BV_SUB)
          .put(Kind.BITVECTOR_MULT, FunctionDeclarationKind.BV_MUL)
          .put(Kind.BITVECTOR_AND, FunctionDeclarationKind.BV_AND)
          .put(Kind.BITVECTOR_OR, FunctionDeclarationKind.BV_OR)
          .put(Kind.BITVECTOR_XOR, FunctionDeclarationKind.BV_XOR)
          .put(Kind.BITVECTOR_SLT, FunctionDeclarationKind.BV_SLT)
          .put(Kind.BITVECTOR_ULT, FunctionDeclarationKind.BV_ULT)
          .put(Kind.BITVECTOR_SLE, FunctionDeclarationKind.BV_SLE)
          .put(Kind.BITVECTOR_ULE, FunctionDeclarationKind.BV_ULE)
          .put(Kind.BITVECTOR_SGT, FunctionDeclarationKind.BV_SGT)
          .put(Kind.BITVECTOR_UGT, FunctionDeclarationKind.BV_UGT)
          .put(Kind.BITVECTOR_SGE, FunctionDeclarationKind.BV_SGE)
          .put(Kind.BITVECTOR_UGE, FunctionDeclarationKind.BV_UGE)
          .put(Kind.BITVECTOR_SDIV, FunctionDeclarationKind.BV_SDIV)
          .put(Kind.BITVECTOR_UDIV, FunctionDeclarationKind.BV_UDIV)
          .put(Kind.BITVECTOR_SREM, FunctionDeclarationKind.BV_SREM)
          // TODO: find out where Kind.BITVECTOR_SMOD fits in here
          .put(Kind.BITVECTOR_UREM, FunctionDeclarationKind.BV_UREM)
          .put(Kind.BITVECTOR_NOT, FunctionDeclarationKind.BV_NOT)
          .put(Kind.BITVECTOR_NEG, FunctionDeclarationKind.BV_NEG)
          .put(Kind.BITVECTOR_EXTRACT, FunctionDeclarationKind.BV_EXTRACT)
          .put(Kind.BITVECTOR_CONCAT, FunctionDeclarationKind.BV_CONCAT)
          .put(Kind.BITVECTOR_SIGN_EXTEND, FunctionDeclarationKind.BV_SIGN_EXTENSION)
          .put(Kind.BITVECTOR_ZERO_EXTEND, FunctionDeclarationKind.BV_ZERO_EXTENSION)
          // Floating-point theory
          .put(Kind.TO_INTEGER, FunctionDeclarationKind.FLOOR)
          .put(Kind.FLOATINGPOINT_TO_SBV, FunctionDeclarationKind.FP_CASTTO_SBV)
          .put(Kind.FLOATINGPOINT_TO_UBV, FunctionDeclarationKind.FP_CASTTO_UBV)
          .put(Kind.FLOATINGPOINT_TO_FP_FROM_FP, FunctionDeclarationKind.FP_CASTTO_FP)
          .put(Kind.FLOATINGPOINT_TO_FP_FROM_SBV, FunctionDeclarationKind.BV_SCASTTO_FP)
          .put(Kind.FLOATINGPOINT_TO_FP_FROM_UBV, FunctionDeclarationKind.BV_UCASTTO_FP)
          .put(Kind.FLOATINGPOINT_IS_NAN, FunctionDeclarationKind.FP_IS_NAN)
          .put(Kind.FLOATINGPOINT_IS_NEG, FunctionDeclarationKind.FP_IS_NEGATIVE)
          .put(Kind.FLOATINGPOINT_IS_INF, FunctionDeclarationKind.FP_IS_INF)
          .put(Kind.FLOATINGPOINT_IS_NORMAL, FunctionDeclarationKind.FP_IS_NORMAL)
          .put(Kind.FLOATINGPOINT_IS_SUBNORMAL, FunctionDeclarationKind.FP_IS_SUBNORMAL)
          .put(Kind.FLOATINGPOINT_IS_ZERO, FunctionDeclarationKind.FP_IS_ZERO)
          .put(Kind.FLOATINGPOINT_EQ, FunctionDeclarationKind.FP_EQ)
          .put(Kind.FLOATINGPOINT_ABS, FunctionDeclarationKind.FP_ABS)
          .put(Kind.FLOATINGPOINT_MAX, FunctionDeclarationKind.FP_MAX)
          .put(Kind.FLOATINGPOINT_MIN, FunctionDeclarationKind.FP_MIN)
          .put(Kind.FLOATINGPOINT_SQRT, FunctionDeclarationKind.FP_SQRT)
          .put(Kind.FLOATINGPOINT_ADD, FunctionDeclarationKind.FP_ADD)
          .put(Kind.FLOATINGPOINT_SUB, FunctionDeclarationKind.FP_SUB)
          .put(Kind.FLOATINGPOINT_MULT, FunctionDeclarationKind.FP_MUL)
          .put(Kind.FLOATINGPOINT_DIV, FunctionDeclarationKind.FP_DIV)
          .put(Kind.FLOATINGPOINT_LT, FunctionDeclarationKind.FP_LT)
          .put(Kind.FLOATINGPOINT_LEQ, FunctionDeclarationKind.FP_LE)
          .put(Kind.FLOATINGPOINT_GT, FunctionDeclarationKind.FP_GT)
          .put(Kind.FLOATINGPOINT_GEQ, FunctionDeclarationKind.FP_GE)
          .put(Kind.FLOATINGPOINT_RTI, FunctionDeclarationKind.FP_ROUND_TO_INTEGRAL)
          .put(Kind.FLOATINGPOINT_TO_FP_FROM_IEEE_BV, FunctionDeclarationKind.FP_FROM_IEEEBV)
          // String and Regex theory
          .put(Kind.STRING_CONCAT, FunctionDeclarationKind.STR_CONCAT)
          .put(Kind.STRING_PREFIX, FunctionDeclarationKind.STR_PREFIX)
          .put(Kind.STRING_SUFFIX, FunctionDeclarationKind.STR_SUFFIX)
          .put(Kind.STRING_CONTAINS, FunctionDeclarationKind.STR_CONTAINS)
          .put(Kind.STRING_SUBSTR, FunctionDeclarationKind.STR_SUBSTRING)
          .put(Kind.STRING_REPLACE, FunctionDeclarationKind.STR_REPLACE)
          .put(Kind.STRING_REPLACE_ALL, FunctionDeclarationKind.STR_REPLACE_ALL)
          .put(Kind.STRING_CHARAT, FunctionDeclarationKind.STR_CHAR_AT)
          .put(Kind.STRING_LENGTH, FunctionDeclarationKind.STR_LENGTH)
          .put(Kind.STRING_INDEXOF, FunctionDeclarationKind.STR_INDEX_OF)
          .put(Kind.STRING_TO_REGEXP, FunctionDeclarationKind.STR_TO_RE)
          .put(Kind.STRING_IN_REGEXP, FunctionDeclarationKind.STR_IN_RE)
          .put(Kind.STRING_FROM_INT, FunctionDeclarationKind.INT_TO_STR)
          .put(Kind.STRING_TO_INT, FunctionDeclarationKind.STR_TO_INT)
          .put(Kind.STRING_LT, FunctionDeclarationKind.STR_LT)
          .put(Kind.STRING_LEQ, FunctionDeclarationKind.STR_LE)
          .put(Kind.REGEXP_PLUS, FunctionDeclarationKind.RE_PLUS)
          .put(Kind.REGEXP_STAR, FunctionDeclarationKind.RE_STAR)
          .put(Kind.REGEXP_OPT, FunctionDeclarationKind.RE_OPTIONAL)
          .put(Kind.REGEXP_CONCAT, FunctionDeclarationKind.RE_CONCAT)
          .put(Kind.REGEXP_UNION, FunctionDeclarationKind.RE_UNION)
          .put(Kind.REGEXP_RANGE, FunctionDeclarationKind.RE_RANGE)
          .put(Kind.REGEXP_INTER, FunctionDeclarationKind.RE_INTERSECT)
          .put(Kind.REGEXP_COMPLEMENT, FunctionDeclarationKind.RE_COMPLEMENT)
          .put(Kind.REGEXP_DIFF, FunctionDeclarationKind.RE_DIFFERENCE)
          .build();

  private FunctionDeclarationKind getDeclarationKind(Term f) {
    try {
      Kind kind = f.getKind();

      // special case: IFF for Boolean, EQ for all other Types
      if (kind == Kind.EQUAL && Iterables.all(f, child -> child.getSort().isBoolean())) {
        return FunctionDeclarationKind.IFF;
      }

      return KIND_MAPPING.getOrDefault(kind, FunctionDeclarationKind.OTHER);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException("Failure trying to get the KIND of Term " + f + ".", e);
    }
  }

  @Override
  protected Term getBooleanVarDeclarationImpl(Term pTFormulaInfo) {
    try {
      Kind kind = pTFormulaInfo.getKind();
      // CONSTANTS are "variables" and Kind.VARIABLEs are bound variables in for example quantifiers
      assert kind == Kind.APPLY_UF || kind == Kind.CONSTANT : pTFormulaInfo.getKind();
      if (kind == Kind.APPLY_UF) {
        // TODO: Test this, this is the old internal implementation
        return pTFormulaInfo.getChild(0);
        // old
        // return pTFormulaInfo.getOperator();
      } else {
        return pTFormulaInfo;
      }
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried reading a bool variable potentially in a UF application that failed. Checked"
              + " term: "
              + pTFormulaInfo
              + ".",
          e);
    }
  }

  @Override
  public Term callFunctionImpl(Term pDeclaration, List<Term> pArgs) {
    if (pArgs.isEmpty()) {
      // CVC5 does not allow argumentless functions! We use variables as a workaround.
      return pDeclaration;
    } else {
      // Applying UFs in CVC5 works with an array of Terms with the UF being the first argument
      // If you pull the children out of it the order will be the same!
      Term[] args =
          Stream.of(new Term[] {pDeclaration}, pArgs.toArray(new Term[0]))
              .flatMap(Stream::of)
              .toArray(Term[]::new);
      return solver.mkTerm(Kind.APPLY_UF, args);
    }
  }

  @Override
  public Term declareUFImpl(String pName, Sort pReturnType, List<Sort> pArgTypes) {
    Term exp = functionsCache.get(pName);

    if (exp == null) {
      if (pArgTypes.isEmpty()) {
        // Ufs in CVC5 can't have 0 arity. I tried an empty array and nullsort.
        // We just use a variable as a workaround
        exp = solver.mkConst(pReturnType, pName);
      } else {
        Sort[] argSorts = pArgTypes.toArray(new Sort[0]);
        // array of argument types and the return type
        Sort ufToReturnType = solver.mkFunctionSort(argSorts, pReturnType);
        exp = solver.mkConst(ufToReturnType, pName);
      }
      functionsCache.put(pName, exp);
    } else {
      Preconditions.checkArgument(
          exp.getSort().equals(exp.getSort()),
          "Symbol %s already in use for different return type %s",
          exp,
          exp.getSort());
      for (int i = 1; i < exp.getNumChildren(); i++) {
        // CVC5s first argument in a function/Uf is the declaration, we don't need that here
        try {
          Preconditions.checkArgument(
              pArgTypes.get(i).equals(exp.getChild(i).getSort()),
              "Argument %s with type %s does not match expected type %s",
              i - 1,
              pArgTypes.get(i),
              exp.getChild(i).getSort());
        } catch (CVC5ApiException e) {
          // Will never be triggered as we don't access beyond the num of children
        }
      }
    }
    return exp;
  }

  @Override
  public Object convertValue(Term expForType, Term value) {
    // Make sure that
    final Sort type = expForType.getSort();
    final Sort valueType = value.getSort();

    // Variables are Kind.CONSTANT and can't be check with isIntegerValue() or getIntegerValue()
    // etc. but only with solver.getValue() and its String serialization
    try {
      if (value.getKind() == Kind.VARIABLE) {
        // VARIABLE == bound variables
        // CVC5 does not allow model values for bound vars; just return the name
        return value.getSymbol();

      } else if (valueType.isInteger() && type.isInteger()) {
        String valueString = solver.getValue(value).toString();
        return new BigInteger(transformString(valueString));

      } else if (valueType.isReal() && type.isReal()) {
        String valueString = transformString(solver.getValue(value).toString());
        if (valueString.contains(".")) {
          BigDecimal rat = new BigDecimal(transformString(valueString));
          return Rational.ofBigDecimal(rat.stripTrailingZeros());
        } else {
          return Rational.of(valueString);
        }

      } else if (valueType.isBitVector()) {
        // CVC5 puts 2 chars (#b) in front of the binary result String
        String valueString = solver.getValue(value).toString();
        return new BigInteger(valueString.substring(2, valueString.length()), 2);

      } else if (valueType.isFloatingPoint()) {
        return parseFloatingPoint(value);

      } else if (type.equals(solver.getBooleanSort())) {
        return solver.getValue(value).equals(solver.mkTrue());

      } else if (value.isStringValue()) {
        return value.getStringValue();

      } else {
        // String serialization for Strings and unknown terms.
        return solver.getValue(value).toString();
      }
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "Failure trying to convert CVC5 " + valueType + " variable into a " + type + " value.",
          e);
    }
  }

  private String transformString(String valueString) {
    // Some numbers have brackets around them
    // i.e. (- 12)
    if (valueString.contains("(")) {
      valueString = valueString.replace("(", "");
      valueString = valueString.replace(")", "");
    }
    // Minus may have a space in between the minus and the num
    if (valueString.contains("- ")) {
      valueString = valueString.replace("- ", "-");
    }
    // Fractions are written in prefix notation and need to be transformed
    if (valueString.contains("/ ")) {
      valueString = valueString.replace("/ ", "");
      valueString = valueString.replace(" ", "/");
    }
    return valueString;
  }

  private Object parseFloatingPoint(Term fpTerm) {
    if (fpTerm.isFloatingPointNaN()) {
      return Float.NaN;
    } else if (fpTerm.isFloatingPointNegInf()) {
      return Float.NEGATIVE_INFINITY;
    } else if (fpTerm.isFloatingPointPosInf()) {
      return Float.POSITIVE_INFINITY;
    } else if (fpTerm.isFloatingPointPosZero()) {
      return BigDecimal.ZERO;
    }
    // Negative zero falls under this category
    String valueString =
        solver.getValue(solver.mkTerm(Kind.FLOATINGPOINT_TO_REAL, fpTerm)).toString();
    return new BigDecimal(valueString).stripTrailingZeros();
  }
}
