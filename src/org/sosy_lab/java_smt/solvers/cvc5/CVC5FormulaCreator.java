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
import com.google.common.primitives.UnsignedInteger;
import com.google.common.primitives.UnsignedLong;
import edu.stanford.CVC4.FloatingPoint;
import edu.stanford.CVC4.FloatingPointSize;
import edu.stanford.CVC4.FunctionType;
import edu.stanford.CVC4.vectorType;
import io.github.cvc5.api.Kind;
import io.github.cvc5.api.Solver;
import io.github.cvc5.api.Sort;
import io.github.cvc5.api.Term;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
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

  private static final Pattern FLOATING_POINT_PATTERN =
      Pattern.compile("^\\(fp #b(?<sign>\\d) #b(?<exp>\\d+) #b(?<mant>\\d+)$");

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
    return solver.mkBitVectorSort(pBitwidth);
  }

  @Override
  public Sort getFloatingPointType(FloatingPointType pType) {
    return solver.mkFloatingPointSort(
        pType.getExponentSize(), pType.getMantissaSize() + 1); // plus sign bit
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
      return FormulaType.getFloatingPointType(
          sort.getFloatingPointExponentSize(),
          sort.getFloatingPointSignificandSize() - 1); // TODO: check for sign bit
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

  private static String getName(Term e) {
    checkState(!e.isNull());
    /* TODO: this will fail most likely
    if (!e.isConst() && !e.isVariable()) {
      e = e.getOperator();
    }*/
    return dequote(e.toString());
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

    if (f.getKind() == Kind.CONSTANT) {
      if (sort.isBoolean()) {
        return visitor.visitConstant(formula, f.getBooleanValue());
      } else if (sort.isReal()) {
        return visitor.visitConstant(formula, f.getRealValue());
      } else if (sort.isInteger()) {
        return visitor.visitConstant(formula, f.getIntegerValue());
      } else if (sort.isBitVector()) {
        return visitor.visitConstant(formula, f.getBitVectorValue());
      } else if (sort.isFloatingPoint()) {
        return visitor.visitConstant(formula, f.getFloatingPointValue());
      } else if (sort.isRoundingMode()) {
        // TODO: this is most likely bullshit and WILL fail!
        return visitor.visitConstant(formula, solver.getRoundingModeSort());
      } else if (sort.isString()) {
        return visitor.visitConstant(formula, f.getStringValue());
      } else {
        throw new UnsupportedOperationException("Unhandled constant " + f + " with Type " + sort);
      }

    } else if (f.getKind() == Kind.VARIABLE) {
      // Bound and unbound vars are the same in CVC5!
      // BOUND vars are used for all vars that are bound to a quantifier in CVC5.
      // We resubstitute them back to the original free.
      // CVC5 doesn't give you the de-brujin index
      Term originalVar = variablesCache.get(formula.toString());
      return visitor.visitBoundVariable(encapsulate(originalVar), 0);

    } else if (f.getKind() == Kind.FORALL || f.getKind() == Kind.EXISTS) {
      // QUANTIFIER: replace bound variable with free variable for visitation
      assert f.getNumChildren() == 2;
      Term body = f.getChildren().get(1);
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

    } else if (f.isVariable()) {
      assert f.getKind() != Kind.BOUND_VARIABLE;
      return visitor.visitFreeVariable(formula, getName(f));

    } else {
      // Termessions like uninterpreted function calls (Kind.APPLY_UF) or operators (e.g. Kind.AND).
      // These are all treated like operators, so we can get the declaration by f.getOperator()!
      List<Formula> args = ImmutableList.copyOf(Iterables.transform(f, this::encapsulate));
      List<FormulaType<?>> argsTypes = new ArrayList<>();
      Term operator = normalize(f.getOperator());
      if (operator.getSort().isFunction()) {
        vectorType argTypes = new FunctionType(operator.getSort()).getArgTypes();
        for (int i = 0; i < argTypes.size(); i++) {
          argsTypes.add(getFormulaTypeFromTermType(argTypes.get(i)));
        }
      } else {
        for (Term arg : f) {
          argsTypes.add(getFormulaType(arg));
        }
      }

      checkState(args.size() == argsTypes.size());

      // TODO some operations (BV_SIGN_EXTEND, BV_ZERO_EXTEND, maybe more) encode information as
      // part of the operator itself, thus the arity is one too small and there might be no
      // possibility to access the information from user side. Should we encode such information as
      // additional parameters? We do so for some methods of Princess.
      return visitor.visitFunction(
          formula,
          args,
          FunctionDeclarationImpl.of(
              getName(f), getDeclarationKind(f), argsTypes, getFormulaType(f), operator));
    }
  }

  /** CVC5 returns new objects when querying operators for UFs. */
  private Term normalize(Term operator) {
    Term function = functionsCache.get(getName(operator));
    if (function != null) {
      checkState(
          Long.compare(function.getId(), operator.getId()) == 0,
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
          .put(Kind.PLUS, FunctionDeclarationKind.ADD)
          .put(Kind.MULT, FunctionDeclarationKind.MUL)
          .put(Kind.MINUS, FunctionDeclarationKind.SUB)
          .put(Kind.DIVISION, FunctionDeclarationKind.DIV)
          .put(Kind.LT, FunctionDeclarationKind.LT)
          .put(Kind.LEQ, FunctionDeclarationKind.LTE)
          .put(Kind.GT, FunctionDeclarationKind.GT)
          .put(Kind.GEQ, FunctionDeclarationKind.GTE)
          // Bitvector theory
          .put(Kind.PLUS, FunctionDeclarationKind.BV_ADD)
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
          .put(Kind.FLOATINGPOINT_TO_FP_FLOATINGPOINT, FunctionDeclarationKind.FP_CASTTO_FP)
          .put(Kind.FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR, FunctionDeclarationKind.BV_SCASTTO_FP)
          .put(Kind.FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR, FunctionDeclarationKind.BV_UCASTTO_FP)
          .put(Kind.FLOATINGPOINT_ISNAN, FunctionDeclarationKind.FP_IS_NAN)
          .put(Kind.FLOATINGPOINT_ISNEG, FunctionDeclarationKind.FP_IS_NEGATIVE)
          .put(Kind.FLOATINGPOINT_ISINF, FunctionDeclarationKind.FP_IS_INF)
          .put(Kind.FLOATINGPOINT_ISN, FunctionDeclarationKind.FP_IS_NORMAL)
          .put(Kind.FLOATINGPOINT_ISSN, FunctionDeclarationKind.FP_IS_SUBNORMAL)
          .put(Kind.FLOATINGPOINT_ISZ, FunctionDeclarationKind.FP_IS_ZERO)
          .put(Kind.FLOATINGPOINT_EQ, FunctionDeclarationKind.FP_EQ)
          .put(Kind.FLOATINGPOINT_ABS, FunctionDeclarationKind.FP_ABS)
          .put(Kind.FLOATINGPOINT_MAX, FunctionDeclarationKind.FP_MAX)
          .put(Kind.FLOATINGPOINT_MIN, FunctionDeclarationKind.FP_MIN)
          .put(Kind.FLOATINGPOINT_SQRT, FunctionDeclarationKind.FP_SQRT)
          .put(Kind.PLUS, FunctionDeclarationKind.FP_ADD)
          .put(Kind.FLOATINGPOINT_SUB, FunctionDeclarationKind.FP_SUB)
          .put(Kind.FLOATINGPOINT_MULT, FunctionDeclarationKind.FP_MUL)
          .put(Kind.FLOATINGPOINT_DIV, FunctionDeclarationKind.FP_DIV)
          .put(Kind.FLOATINGPOINT_LT, FunctionDeclarationKind.FP_LT)
          .put(Kind.FLOATINGPOINT_LEQ, FunctionDeclarationKind.FP_LE)
          .put(Kind.FLOATINGPOINT_GT, FunctionDeclarationKind.FP_GT)
          .put(Kind.FLOATINGPOINT_GEQ, FunctionDeclarationKind.FP_GE)
          .put(Kind.FLOATINGPOINT_RTI, FunctionDeclarationKind.FP_ROUND_TO_INTEGRAL)
          .put(Kind.FLOATINGPOINT_TO_FP_IEEE_BITVECTOR, FunctionDeclarationKind.FP_AS_IEEEBV)
          // String and Regex theory
          .put(Kind.STRING_CONCAT, FunctionDeclarationKind.STR_CONCAT)
          .put(Kind.STRING_PREFIX, FunctionDeclarationKind.STR_PREFIX)
          .put(Kind.STRING_SUFFIX, FunctionDeclarationKind.STR_SUFFIX)
          .put(Kind.STRING_STRCTN, FunctionDeclarationKind.STR_CONTAINS)
          .put(Kind.STRING_SUBSTR, FunctionDeclarationKind.STR_SUBSTRING)
          .put(Kind.STRING_STRREPL, FunctionDeclarationKind.STR_REPLACE)
          .put(Kind.STRING_STRREPLALL, FunctionDeclarationKind.STR_REPLACE_ALL)
          .put(Kind.STRING_CHARAT, FunctionDeclarationKind.STR_CHAR_AT)
          .put(Kind.STRING_LENGTH, FunctionDeclarationKind.STR_LENGTH)
          .put(Kind.STRING_STRIDOF, FunctionDeclarationKind.STR_INDEX_OF)
          .put(Kind.STRING_TO_REGEXP, FunctionDeclarationKind.STR_TO_RE)
          .put(Kind.STRING_IN_REGEXP, FunctionDeclarationKind.STR_IN_RE)
          .put(Kind.STRING_STOI, FunctionDeclarationKind.STR_TO_INT)
          .put(Kind.STRING_ITOS, FunctionDeclarationKind.INT_TO_STR)
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
    Kind kind = f.getKind();

    // special case: IFF for Boolean, EQ for all other Types
    if (kind == Kind.EQUAL && Iterables.all(f, child -> child.getType().isBoolean())) {
      return FunctionDeclarationKind.IFF;
    }

    return KIND_MAPPING.getOrDefault(kind, FunctionDeclarationKind.OTHER);
  }

  @Override
  protected Term getBooleanVarDeclarationImpl(Term pTFormulaInfo) {
    Kind kind = pTFormulaInfo.getKind();
    assert kind == Kind.APPLY_UF || kind == Kind.VARIABLE : pTFormulaInfo.getKind();
    if (kind == Kind.APPLY_UF) {
      return pTFormulaInfo.getOperator();
    } else {
      return pTFormulaInfo;
    }
  }

  @Override
  public Term callFunctionImpl(Term pDeclaration, List<Term> pArgs) {
    if (pArgs.isEmpty()) {
      return TermManager.mkTerm(pDeclaration);
    } else {
      vectorTerm args = new vectorTerm();
      for (Term Term : pArgs) {
        args.add(Term);
      }
      return TermManager.mkTerm(pDeclaration, args);
    }
  }

  @Override
  public Term declareUFImpl(String pName, Type pReturnType, List<Type> pArgTypes) {
    Term exp = functionsCache.get(pName);
    if (exp == null) {
      vectorType args = new vectorType();
      for (Type t : pArgTypes) {
        args.add(t);
      }
      exp = TermManager.mkVar(pName, TermManager.mkFunctionType(args, pReturnType));
      functionsCache.put(pName, exp);
    }
    return exp;
  }

  @Override
  public Object convertValue(Term expForType, Term value) {
    final Type Type = expForType.getType();
    final Type valueType = value.getType();
    if (value.getKind() == Kind.BOUND_VARIABLE) {
      // CVC5 does not allow model values for bound vars
      return value.toString();
    } else if (valueType.isBoolean()) {
      return value.getConstBoolean();

    } else if (valueType.isInteger() && Type.isInteger()) {
      return new BigInteger(value.getConstRational().toString());

    } else if (valueType.isReal() && Type.isReal()) {
      Rational rat = value.getConstRational();
      return org.sosy_lab.common.rationals.Rational.of(
          new BigInteger(rat.getNumerator().toString()),
          new BigInteger(rat.getDenominator().toString()));

    } else if (valueType.isBitVector()) {
      Integer bv = value.getConstBitVector().getValue();
      if (bv.fitsSignedLong()) {
        return BigInteger.valueOf(bv.getUnsignedLong());
      } else {
        return value.toString(); // default
      }

    } else if (valueType.isFloatingPoint()) {
      return parseFloatingPoint(value);

    } else if (valueType.isString()) {
      return value.getConstString().toString();

    } else {
      // String serialization for unknown terms.
      return value.toString();
    }
  }

  private Object parseFloatingPoint(Term fpTerm) {
    Matcher matcher = FLOATING_POINT_PATTERN.matcher(fpTerm.toString());
    if (!matcher.matches()) {
      throw new NumberFormatException("Unknown floating-point format: " + fpTerm);
    }

    FloatingPoint fp = fpTerm.getConstFloatingPoint();
    FloatingPointSize fpType = fp.getT();
    long expWidth = fpType.exponentWidth();
    long mantWidth = fpType.significandWidth() - 1; // without sign bit

    assert matcher.group("sign").length() == 1;
    assert matcher.group("exp").length() == expWidth;
    assert matcher.group("mant").length() == mantWidth;

    String str = matcher.group("sign") + matcher.group("exp") + matcher.group("mant");
    if (expWidth == 11 && mantWidth == 52) {
      return Double.longBitsToDouble(UnsignedLong.valueOf(str, 2).longValue());
    } else if (expWidth == 8 && mantWidth == 23) {
      return Float.intBitsToFloat(UnsignedInteger.valueOf(str, 2).intValue());
    }

    // TODO to be fully correct, we would need to interpret this string
    return fpTerm.toString();
  }
}
