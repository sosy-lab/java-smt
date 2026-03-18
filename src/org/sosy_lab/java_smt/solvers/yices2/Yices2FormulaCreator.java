// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Table;
import com.google.common.primitives.Ints;
import com.sri.yices.BigRational;
import com.sri.yices.Constructor;
import com.sri.yices.ProductComponent;
import com.sri.yices.SumComponent;
import com.sri.yices.Terms;
import com.sri.yices.Types;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.yices2.Yices2Formula.Yices2ArrayFormula;
import org.sosy_lab.java_smt.solvers.yices2.Yices2Formula.Yices2BitvectorFormula;
import org.sosy_lab.java_smt.solvers.yices2.Yices2Formula.Yices2BooleanFormula;
import org.sosy_lab.java_smt.solvers.yices2.Yices2Formula.Yices2IntegerFormula;
import org.sosy_lab.java_smt.solvers.yices2.Yices2Formula.Yices2RationalFormula;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
class Yices2FormulaCreator extends FormulaCreator<Integer, Integer, Long, Integer> {

  /**
   * Maps a name and a free variable or function type to a concrete formula node. We allow only 1
   * type per var name, meaning there is only 1 column per row!
   */
  private final Table<String, Integer, Integer> formulaCache = HashBasedTable.create();

  /**
   * List of all UF function declarations.
   *
   * <p>We need this in the visitor to tell the difference between functions and arrays. Both are
   * modeled internally by function terms.
   */
  private final Set<Integer> ufSymbols = new HashSet<>();

  Yices2FormulaCreator() {
    super(null, Types.boolType(), Types.intType(), Types.realType(), null, null);
  }

  @Override
  public Integer getBitvectorType(int pBitwidth) {
    return Types.bvType(pBitwidth);
  }

  @Override
  public Integer getFloatingPointType(FloatingPointType pType) {
    throw new UnsupportedOperationException();
  }

  @Override
  public Integer getArrayType(Integer pIndexType, Integer pElementType) {
    return Types.functionType(pIndexType, pElementType);
  }

  @Override
  public Integer makeVariable(Integer pType, String pVarName) {
    return createNamedVariable(pType, pVarName);
  }

  @Override
  public Integer extractInfo(Formula pT) {
    return Yices2FormulaManager.getYicesTerm(pT);
  }

  @Override
  @SuppressWarnings("unchecked")
  protected <TI extends Formula, TE extends Formula> FormulaType<TE> getArrayFormulaElementType(
      ArrayFormula<TI, TE> pArray) {
    return ((Yices2ArrayFormula<TI, TE>) pArray).getElementType();
  }

  @Override
  @SuppressWarnings("unchecked")
  protected <TI extends Formula, TE extends Formula> FormulaType<TI> getArrayFormulaIndexType(
      ArrayFormula<TI, TE> pArray) {
    return ((Yices2ArrayFormula<TI, TE>) pArray).getIndexType();
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, Integer pTerm) {
    // INTEGER is basic type and also used for function applications like EXTRACT/EXPAND.
    // RATIONAL can be used to model INTEGERS. Otherwise, the type should match exactly.
    assert FormulaType.IntegerType.equals(pType)
            || (FormulaType.RationalType.equals(pType)
                && FormulaType.IntegerType.equals(getFormulaType(pTerm)))
            || pType.equals(getFormulaType(pTerm))
        : String.format(
            "Trying to encapsulate formula %s of type %s as %s",
            Terms.toString(pTerm), getFormulaType(pTerm), pType);
    if (pType.isBooleanType()) {
      return (T) new Yices2BooleanFormula(pTerm);
    } else if (pType.isIntegerType()) {
      return (T) new Yices2IntegerFormula(pTerm);
    } else if (pType.isRationalType()) {
      return (T) new Yices2RationalFormula(pTerm);
    } else if (pType.isBitvectorType()) {
      return (T) new Yices2BitvectorFormula(pTerm);
    } else if (pType.isArrayType()) {
      var range = ((ArrayFormulaType<?, ?>) pType).getElementType();
      var dom = ((ArrayFormulaType<?, ?>) pType).getIndexType();
      return (T) encapsulateArray(pTerm, dom, range);
    }
    throw new IllegalArgumentException("Cannot create formulas of type " + pType + " in Yices");
  }

  @Override
  public BooleanFormula encapsulateBoolean(Integer pTerm) {
    assert getFormulaType(pTerm).isBooleanType();
    return new Yices2BooleanFormula(pTerm);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Integer pTerm) {
    assert getFormulaType(pTerm).isBitvectorType();
    return new Yices2BitvectorFormula(pTerm);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      Integer pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    checkArgument(
        getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType)),
        "Array formula has unexpected type: %s",
        getFormulaType(pTerm));
    return new Yices2Formula.Yices2ArrayFormula<>(pTerm, pIndexType, pElementType);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    if (pFormula instanceof BitvectorFormula) {
      int type = Terms.typeOf(extractInfo(pFormula));
      return (FormulaType<T>) FormulaType.getBitvectorTypeWithSize(Types.bvSize(type));
    } else if (pFormula instanceof ArrayFormula) {
      return (FormulaType<T>) convertType(Terms.typeOf(extractInfo(pFormula)));
    } else {
      return super.getFormulaType(pFormula);
    }
  }

  @Override
  public FormulaType<?> getFormulaType(Integer pFormula) {
    return convertType(Terms.typeOf(pFormula));
  }

  /** Convert from Yices2 types to JavaSMT FormulaTypes. */
  private FormulaType<?> convertType(Integer pType) {
    if (Types.isBool(pType)) {
      return FormulaType.BooleanType;
    } else if (Types.isInt(pType)) {
      return FormulaType.IntegerType;
    } else if (Types.isReal(pType)) {
      return FormulaType.RationalType;
    } else if (Types.isBitvector(pType)) {
      return FormulaType.getBitvectorTypeWithSize(Types.bvSize(pType));
    } else if (Types.isFunction(pType)) {
      var domain = Types.child(pType, 0);
      var range = Types.child(pType, 1);
      return FormulaType.getArrayType(convertType(domain), convertType(range));
    } else {
      throw new IllegalArgumentException(
          String.format("Unknown formula type '%s'", Types.toString(pType)));
    }
  }

  /** Creates a named, free variable. Might retrieve it from the cache if created prior. */
  protected int createNamedVariable(int type, String name) {
    Integer maybeFormula = formulaCache.get(name, type);
    if (maybeFormula != null) {
      return maybeFormula;
    }
    checkArgument(
        !formulaCache.containsRow(name),
        "Symbol '%s' already used for a variable of type '%s'",
        name,
        formulaCache.containsRow(name)
            ? Types.toString(formulaCache.row(name).keySet().iterator().next())
            : "");

    int var = Terms.newUninterpretedTerm(type);
    // Names in Yices2 behave like a stack. The last variable named is retrieved when asking for
    // a term with a specific name. Since we substitute free vars with bound for quantifiers,
    // this sometimes mixes them up, hence we track them ourselves.
    Terms.setName(var, name);
    formulaCache.put(name, type, var);
    return var;
  }

  protected int createBoundVariableFromFreeVariable(int unboundVar) {
    int type = Terms.typeOf(unboundVar);
    String name = Terms.getName(unboundVar);

    // Search for recently created bound variables and re-use it
    // (Names work like a stack in Yices2. If we associate a term with a name, we get that term
    // if we ask yices_get_term_by_name(). However, if we create bound variables, we associate
    // them with the same name as the free variable (so that it has the same name). This pushes the
    // name stack, and we get the bound var when asking yices_get_term_by_name(). We want to
    // re-use the bound variables here, but never the free ones.)
    int termFromName = Terms.getByName(name);
    if (termFromName != -1) {
      int termFromNameType = Terms.typeOf(termFromName);
      checkArgument(
          type == termFromNameType,
          "Cannot override symbol '%s' with new symbol '%s' of type '%s'",
          Types.toString(termFromNameType),
          name,
          Types.toString(type));
      Constructor constructor = Terms.constructor(termFromName);
      if (constructor == Constructor.VARIABLE) {
        // Already a bound var
        return termFromName;
      }
    }

    // reset term name binding
    // TODO: add yices_remove_term_name();
    int bound = Terms.newVariable(type);
    // Names in Yices2 behave like a stack. The last variable named is retrieved when asking for
    // a term with a specific name. Since we substitute free vars with bound for quantifiers,
    // this sometimes mixes them up, hence we track them ourselves.
    // This overrides the naming, but the old is cached.
    // Meaning that if we remove the new name, the old term gets its name back.
    // Since we just want to retrieve the same var for the quantifier we are currently building,
    // this is fine.
    Terms.setName(bound, name);
    return bound;
  }

  /**
   * Returns the name of a variable or uf term.
   *
   * <p>Will return an abstract value name if the term has no name. Yices may introduce unnamed
   * terms while rewriting bv operations
   */
  private String lookupName(int term) {
    return Terms.getName(term) == null ? "@" + term : Terms.getName(term);
  }

  @Override
  public <R> R visit(FormulaVisitor<R> pVisitor, Formula pFormula, Integer pF) {
    Constructor constructor = Terms.constructor(pF);
    switch (constructor) {
      case BOOL_CONSTANT:
        return pVisitor.visitConstant(pFormula, Terms.boolConstValue(pF));
      case ARITH_CONSTANT:
        return pVisitor.visitConstant(pFormula, convertValue(pF, pF));
      case BV_CONSTANT:
        return pVisitor.visitConstant(pFormula, convertValue(pF, pF));
      case LAMBDA_TERM:
        // We use lambda terms as array constants
        return pVisitor.visitFunction(
            pFormula,
            ImmutableList.of(encapsulateWithTypeOf(Terms.child(pF, 1))),
            FunctionDeclarationImpl.of(
                "const",
                FunctionDeclarationKind.CONST,
                ImmutableList.of(getFormulaType(Terms.child(pF, 1))),
                getFormulaType(pF),
                0));
      case FORALL_TERM:
        return visitQuantifier(pVisitor, pFormula, pF, Quantifier.FORALL);
      case UNINTERPRETED_TERM:
        return pVisitor.visitFreeVariable(pFormula, lookupName(pF));
      default:
        return visitFunctionApplication(pVisitor, pFormula, pF, constructor);
    }
  }

  private <R> R visitQuantifier(
      FormulaVisitor<R> pVisitor, Formula pFormula, Integer pF, Quantifier pQuantifier) {

    // in Yices2QuantifierManager, we replace fre variables with bound variables.
    // Here, we revert this replacement and provide free variables towards the user.
    List<Integer> args = getArgs(pF);
    int[] boundVars = Ints.toArray(args.subList(0, args.size() - 1));
    int[] freeVars = new int[boundVars.length];
    for (int i = 0; i < boundVars.length; i++) {
      // use from cached variable mapping
      freeVars[i] = createNamedVariable(Terms.typeOf(boundVars[i]), Terms.getName(boundVars[i]));
    }

    int body = Iterables.getLast(args);
    if (pQuantifier == Quantifier.EXISTS) {
      body = Terms.not(body); // EXISTS is an alias for NOT(FORALL(x, NOT(body)))
    }
    int substBody = Terms.subst(body, boundVars, freeVars);

    return pVisitor.visitQuantifier(
        (BooleanFormula) pFormula,
        pQuantifier,
        Ints.asList(freeVars).stream()
            .map(this::encapsulateWithTypeOf)
            .collect(Collectors.toList()),
        encapsulateBoolean(substBody));
  }

  private <R> R visitFunctionApplication(
      FormulaVisitor<R> pVisitor, Formula pFormula, int pF, final Constructor constructor) {
    // filled later, except for some special function applications
    String functionName = null;
    Integer functionDeclaration = null;
    List<Integer> functionArgs = null;
    List<Integer> functionIndex = ImmutableList.of();

    // filled directly when handling the function application
    FunctionDeclarationKind functionKind;

    switch (constructor) {
      case ITE_TERM:
        functionKind = FunctionDeclarationKind.ITE;
        break;
      case APP_TERM:
        var fun = Terms.child(pF, 0);
        if (ufSymbols.contains(fun)) {
          functionKind = FunctionDeclarationKind.UF;
          var args = getArgs(pF);
          var f = args.get(0);
          var x = FluentIterable.from(args).skip(1).toList();
          functionName = lookupName(f);
          functionDeclaration = f;
          functionArgs = x;
        } else {
          functionKind = FunctionDeclarationKind.SELECT;
          functionArgs = getArgs(pF);
          functionName = "select";
          var f = Terms.newVariable(Terms.typeOf(functionArgs.get(0)));
          var x = Terms.newVariable(Terms.typeOf(functionArgs.get(1)));
          functionDeclaration = Terms.lambda(new int[] {f, x}, Terms.funApplication(f, x));
        }
        break;
      case UPDATE_TERM:
        functionKind = FunctionDeclarationKind.STORE;
        functionArgs = getArgs(pF);
        var f = Terms.newVariable(Terms.typeOf(functionArgs.get(0)));
        var x = Terms.newVariable(Terms.typeOf(functionArgs.get(1)));
        var y = Terms.newVariable(Terms.typeOf(functionArgs.get(2)));
        functionDeclaration = Terms.lambda(new int[] {f, x, y}, Terms.functionUpdate1(f, x, y));
        break;
      case EQ_TERM:
        functionKind = FunctionDeclarationKind.EQ;
        break;
      case DISTINCT_TERM:
        functionKind = FunctionDeclarationKind.DISTINCT;
        break;
      case NOT_TERM:
        if (isNestedExists(pF)) {
          int existsTerm = Iterables.getOnlyElement(getArgs(pF));
          return visitQuantifier(pVisitor, pFormula, existsTerm, Quantifier.EXISTS);
        } else if (isNestedConjunction(pF)) {
          functionKind = FunctionDeclarationKind.AND;
          functionArgs = getNestedConjunctionArgs(pF);
        } else {
          functionKind = FunctionDeclarationKind.NOT;
        }
        break;
      case OR_TERM:
        functionKind = FunctionDeclarationKind.OR;
        break;
      case XOR_TERM:
        functionKind = FunctionDeclarationKind.XOR;
        break;
      case BV_DIV:
        functionKind = FunctionDeclarationKind.BV_UDIV;
        break;
      case BV_REM:
        functionKind = FunctionDeclarationKind.BV_UREM;
        break;
      case BV_SDIV:
        functionKind = FunctionDeclarationKind.BV_SDIV;
        break;
      case BV_SREM:
        functionKind = FunctionDeclarationKind.BV_SREM;
        break;
      case BV_SMOD:
        functionKind = FunctionDeclarationKind.BV_SMOD;
        break;
      case BV_SHL:
        functionKind = FunctionDeclarationKind.BV_SHL;
        break;
      case BV_LSHR:
        functionKind = FunctionDeclarationKind.BV_LSHR;
        break;
      case BV_ASHR:
        functionKind = FunctionDeclarationKind.BV_ASHR;
        break;
      case BV_GE_ATOM:
        functionKind = FunctionDeclarationKind.BV_UGE;
        break;
      case BV_SGE_ATOM:
        functionKind = FunctionDeclarationKind.BV_SGE;
        break;
      case ARITH_GE_ATOM:
        functionKind = FunctionDeclarationKind.GTE;
        break;
      case FLOOR:
        functionKind = FunctionDeclarationKind.FLOOR;
        break;
      case RDIV:
        functionKind = FunctionDeclarationKind.DIV;
        break;
      case IDIV:
        functionKind = FunctionDeclarationKind.DIV;
        break;
      case SELECT_TERM:
        functionKind = FunctionDeclarationKind.SELECT;
        break;
      case BV_SUM:
        if (Terms.numChildren(pF) == 1) {
          functionKind = FunctionDeclarationKind.BV_MUL;
          functionArgs = getOnlySumTerm(pF);
        } else {
          functionKind = FunctionDeclarationKind.BV_ADD;
          functionArgs = getSumTerms(pF);
        }
        break;
      case ARITH_SUM:
        if (Terms.numChildren(pF) == 1) {
          functionKind = FunctionDeclarationKind.MUL;
          functionArgs = getOnlySumTerm(pF);
        } else {
          functionKind = FunctionDeclarationKind.ADD;
          functionArgs = getSumTerms(pF);
        }
        break;
      case POWER_PRODUCT:
        if (Terms.isBitvector(pF)) {
          functionKind = FunctionDeclarationKind.BV_MUL;
          functionArgs = getProductFactors(pF);
          // TODO Product of more then 2 bitvectors ?
        } else {
          functionKind = FunctionDeclarationKind.MUL;
          functionArgs = getProductFactors(pF);
        }
        break;
      case BIT_TERM:
        // FIXME Not really "extract"
        functionKind = FunctionDeclarationKind.BV_EXTRACT;
        functionIndex = ImmutableList.of(Terms.projIndex(pF));
        functionArgs = ImmutableList.of(Terms.projArg(pF));
        break;
      case BV_ARRAY:
        // FIXME Not really "concat"
        functionKind = FunctionDeclarationKind.BV_CONCAT;
        break;
      default:
        functionKind = FunctionDeclarationKind.OTHER;
    }

    if (functionName == null) {
      functionName = functionKind.toString();
    }
    if (functionArgs == null) {
      functionArgs = getArgs(pF);
    }
    if (functionDeclaration == null) {
      functionDeclaration = buildDeclaration(functionKind, functionIndex, functionArgs);
    }

    final ImmutableList<FormulaType<?>> argTypes =
        ImmutableList.copyOf(Lists.transform(functionArgs, this::getFormulaType));

    Preconditions.checkState(
        functionArgs.size() == argTypes.size(),
        "different size of args (%s) and their types (%s) in term %s",
        functionArgs,
        argTypes,
        pFormula);

    final ImmutableList.Builder<Formula> argsBuilder = ImmutableList.builder();
    for (int i = 0; i < functionArgs.size(); i++) {
      argsBuilder.add(encapsulate(argTypes.get(i), functionArgs.get(i)));
    }
    final ImmutableList<Formula> args = argsBuilder.build();

    return pVisitor.visitFunction(
        pFormula,
        args,
        FunctionDeclarationImpl.of(
            functionName, functionKind, argTypes, getFormulaType(pF), functionDeclaration));
  }

  private int buildDeclaration(
      FunctionDeclarationKind pKind, List<Integer> pIndex, List<Integer> pArgs) {
    ImmutableList.Builder<Integer> builder = ImmutableList.builder();
    int c = 0;
    for (var arg : pArgs) {
      builder.add(Terms.newVariable("var" + c++, Terms.typeOf(arg)));
    }
    var args = builder.build();
    int f;
    switch (pKind) {
      case AND:
        f = Terms.and(args);
        break;
      case NOT:
        checkArgument(args.size() == 1);
        f = Terms.not(args.get(0));
        break;
      case OR:
        f = Terms.or(args);
        break;
      case IFF:
        checkArgument(args.size() == 2);
        f = Terms.iff(args.get(0), args.get(1));
        break;
      case ITE:
        checkArgument(args.size() == 3);
        f = Terms.ifThenElse(args.get(0), args.get(1), args.get(2));
        break;
      case XOR:
        f = Terms.xor(args);
        break;
      case IMPLIES:
        checkArgument(args.size() == 2);
        f = Terms.implies(args.get(0), args.get(1));
        break;
      case DISTINCT:
        f = Terms.distinct(args);
        break;
      case STORE:
        checkArgument(args.size() == 3);
        f = Terms.functionUpdate1(args.get(0), args.get(1), args.get(2));
        break;
      case SELECT:
        checkArgument(args.size() == 2);
        f = Terms.funApplication(args.get(0), args.get(1));
        break;
      case CONST:
        checkArgument(args.size() == 1);
        f = Terms.lambda(new int[] {}, args.get(0));
        break;
      case UMINUS:
        checkArgument(args.size() == 1);
        f = Terms.neg(args.get(0));
        break;
      case SUB:
        checkArgument(args.size() == 2);
        f = Terms.sub(args.get(0), args.get(1));
        break;
      case ADD:
        f = Terms.add(args);
        break;
      case DIV:
        checkArgument(args.size() == 2);
        f = Terms.div(args.get(0), args.get(1));
        break;
      case MUL:
        checkArgument(args.size() == 2);
        f = Terms.mul(args.get(0), args.get(1));
        break;
      case MODULO:
        checkArgument(args.size() == 2);
        f = Terms.imod(args.get(0), args.get(1));
        break;
      case UF:
      case VAR:
        throw new IllegalArgumentException("Expecting builtin kind");
      case LT:
        checkArgument(args.size() == 2);
        f = Terms.arithLt(args.get(0), args.get(1));
        break;
      case LTE:
        checkArgument(args.size() == 2);
        f = Terms.arithLeq(args.get(0), args.get(1));
        break;
      case GT:
        checkArgument(args.size() == 2);
        f = Terms.arithGt(args.get(0), args.get(1));
        break;
      case GTE:
        checkArgument(args.size() == 2);
        f = Terms.arithGeq(args.get(0), args.get(1));
        break;
      case EQ:
        checkArgument(args.size() == 2);
        f = Terms.eq(args.get(0), args.get(1));
        break;
      case EQ_ZERO:
        throw new UnsupportedOperationException("EQ_ZERO not supported");
      case GTE_ZERO:
        throw new UnsupportedOperationException("GTE_ZERO not supported");
      case FLOOR:
        checkArgument(args.size() == 1);
        f = Terms.floor(args.get(0));
        break;
      case TO_REAL:
        throw new UnsupportedOperationException("TO_REAL not supported");
      case INT_TO_BV:
        throw new UnsupportedOperationException("INT_TO_BV not supported");
      case BV_EXTRACT:
        checkArgument(args.size() == 1);
        f = Terms.bvExtractBit(args.get(0), pIndex.get(0));
        // FIXME Should be:
        // f = Terms.bvExtract(args.get(0), pIndex.get(0), pIndex.get(1));
        break;
      case BV_CONCAT:
        f = Terms.bvFromBoolArray(args);
        // FIXME Should be:
        // f = Terms.bvConcat(args);
        break;
      case BV_SIGN_EXTENSION:
        checkArgument(args.size() == 1);
        f = Terms.bvSignExtend(args.get(0), pIndex.get(0));
        break;
      case BV_ZERO_EXTENSION:
        checkArgument(args.size() == 1);
        f = Terms.bvZeroExtend(args.get(0), pIndex.get(0));
        break;
      case BV_NOT:
        checkArgument(args.size() == 1);
        f = Terms.bvNot(args.get(0));
        break;
      case BV_NEG:
        checkArgument(args.size() == 1);
        f = Terms.bvNeg(args.get(0));
        break;
      case BV_OR:
        f = Terms.bvOr(args);
        break;
      case BV_AND:
        f = Terms.bvAnd(args);
        break;
      case BV_XOR:
        f = Terms.bvXor(args);
        break;
      case BV_SUB:
        checkArgument(args.size() == 2);
        f = Terms.bvSub(args.get(0), args.get(1));
        break;
      case BV_ADD:
        f = Terms.bvAdd(args);
        break;
      case BV_SDIV:
        checkArgument(args.size() == 2);
        f = Terms.bvSDiv(args.get(0), args.get(1));
        break;
      case BV_UDIV:
        checkArgument(args.size() == 2);
        f = Terms.bvDiv(args.get(0), args.get(1));
        break;
      case BV_SREM:
        checkArgument(args.size() == 2);
        f = Terms.bvSRem(args.get(0), args.get(1));
        break;
      case BV_UREM:
        checkArgument(args.size() == 2);
        f = Terms.bvRem(args.get(0), args.get(1));
        break;
      case BV_SMOD:
        checkArgument(args.size() == 2);
        f = Terms.bvSMod(args.get(0), args.get(1));
        break;
      case BV_MUL:
        checkArgument(args.size() == 2);
        f = Terms.bvMul(args.get(0), args.get(1));
        break;
      case BV_ULT:
        checkArgument(args.size() == 2);
        f = Terms.bvLt(args.get(0), args.get(1));
        break;
      case BV_SLT:
        checkArgument(args.size() == 2);
        f = Terms.bvSLt(args.get(0), args.get(1));
        break;
      case BV_ULE:
        checkArgument(args.size() == 2);
        f = Terms.bvLe(args.get(0), args.get(1));
        break;
      case BV_SLE:
        checkArgument(args.size() == 2);
        f = Terms.bvSLe(args.get(0), args.get(1));
        break;
      case BV_UGT:
        checkArgument(args.size() == 2);
        f = Terms.bvGt(args.get(0), args.get(1));
        break;
      case BV_SGT:
        checkArgument(args.size() == 2);
        f = Terms.bvSGt(args.get(0), args.get(1));
        break;
      case BV_UGE:
        checkArgument(args.size() == 2);
        f = Terms.bvGe(args.get(0), args.get(1));
        break;
      case BV_SGE:
        checkArgument(args.size() == 2);
        f = Terms.bvSGe(args.get(0), args.get(1));
        break;
      case BV_EQ:
        checkArgument(args.size() == 2);
        f = Terms.bvEq(args.get(0), args.get(1));
        break;
      case BV_SHL:
        checkArgument(args.size() == 2);
        f = Terms.bvShl(args.get(0), args.get(1));
        break;
      case BV_LSHR:
        checkArgument(args.size() == 2);
        f = Terms.bvLshr(args.get(0), args.get(1));
        break;
      case BV_ASHR:
        checkArgument(args.size() == 2);
        f = Terms.bvAshr(args.get(0), args.get(1));
        break;
      case BV_ROTATE_LEFT:
        throw new UnsupportedOperationException("BV_ROTATE_LEFT not supported");
      case BV_ROTATE_RIGHT:
        throw new UnsupportedOperationException("BV_ROTATE_RIGHT not supported");
      case BV_ROTATE_LEFT_BY_INT:
        checkArgument(args.size() == 1);
        f = Terms.bvRotateLeft(args.get(0), pIndex.get(0));
        break;
      case BV_ROTATE_RIGHT_BY_INT:
        checkArgument(args.size() == 1);
        f = Terms.bvRotateRight(args.get(0), pIndex.get(0));
        break;
      case UBV_TO_INT:
        throw new UnsupportedOperationException("UBV_TO_INT not supported");
      case SBV_TO_INT:
        throw new UnsupportedOperationException("SBV_TO_INT not supported");
      case OTHER:
        throw new UnsupportedOperationException("OTHER not supported");
      default:
        throw new UnsupportedOperationException();
    }
    return Terms.lambda(args, f);
  }

  /**
   * Yices transforms <code>EXISTS(x, body)</code> into <code>NOT(FORALL(x, NOT(body)))</code>. See
   * <a
   * href="https://github.com/SRI-CSL/yices2/blob/fda0a325ea7923f152ea9f9a5d20eddfd1d96224/src/io/term_printer.c#L1947">sources
   * of Yices</a>.
   */
  private static boolean isNestedExists(int outerTerm) {
    return Terms.constructor(outerTerm) == Constructor.NOT_TERM
        && Terms.constructor(Terms.child(outerTerm, 0)) == Constructor.FORALL_TERM;
  }

  /** Yices transforms <code>AND(x,...)</code> into <code>NOT(OR(NOT(X),NOT(...))</code>. */
  private static boolean isNestedConjunction(int outerTerm) {
    return Terms.constructor(outerTerm) == Constructor.NOT_TERM
        && Terms.constructor(Terms.child(outerTerm, 0)) == Constructor.OR_TERM;
  }

  /**
   * Yices transforms <code>AND(x,...)</code> into <code>NOT(OR(NOT(X),NOT(...))</code>.
   *
   * <p>Only call this method for terms that are nested conjunctions!
   */
  private static List<Integer> getNestedConjunctionArgs(int outerTerm) {
    checkArgument(Terms.constructor(outerTerm) == Constructor.NOT_TERM);
    int middleTerm = Terms.child(outerTerm, 0);
    checkArgument(Terms.constructor(middleTerm) == Constructor.OR_TERM);
    List<Integer> result = new ArrayList<>();
    for (int child : getArgs(middleTerm)) {
      result.add(Terms.not(child));
    }
    return result;
  }

  private static List<Integer> getArgs(int parent) {
    ImmutableList.Builder<Integer> children = ImmutableList.builder();
    for (int i = 0; i < Terms.numChildren(parent); i++) {
      children.add(Terms.child(parent, i));
    }
    return children.build();
  }

  /** <code>1</code> for the given theory. */
  private static int mkOne(int type) {
    if (Types.isArithmetic(type)) {
      return Terms.one();
    } else if (Types.isBitvector(type)) {
      return Terms.bvOne(Types.bvSize(type));
    } else {
      throw new IllegalArgumentException();
    }
  }

  /** Convert value to constant term. */
  private static int toConstant(Object value) {
    if (value instanceof BigRational) {
      var rational = (BigRational) value;
      if (rational.isInteger()) {
        return Terms.intConst(rational.getNumerator());
      } else {
        return Terms.rationalConst(rational);
      }
    } else if (value instanceof boolean[]) {
      var array = (boolean[]) value;
      ImmutableList.Builder<Integer> builder = ImmutableList.builder();
      for (var bit : array) {
        builder.add(bit ? 1 : 0);
      }
      return Terms.bvConst(builder.build());
    } else {
      throw new IllegalArgumentException();
    }
  }

  /** Multiply two arithmetic or bv terms. */
  private static int mkMultiply(int a, int b) {
    if (Terms.isArithmetic(a) && Terms.isArithmetic(b)) {
      return Terms.mul(a, b);
    } else if (Terms.isBitvector(a) && Terms.isBitvector(b)) {
      return Terms.bvMul(a, b);
    } else {
      throw new IllegalArgumentException();
    }
  }

  /* Power of a bv or an arithmetic term. */
  private static int mkPower(int term, int exponent) {
    if (Terms.isArithmetic(term)) {
      return Terms.power(term, exponent);
    } else if (Terms.isBitvector(term)) {
      return Terms.bvPower(term, exponent);
    } else {
      throw new IllegalArgumentException();
    }
  }

  /**
   * Returns a list of terms for a sum.
   *
   * <p>Splits a sum <code>a*t1 + b*t2 + ...</code> into a list of terms <code>a*t1</code>, <code>
   * b*t2</code>, ...
   */
  private static List<Integer> getSumTerms(int parent) {
    ImmutableList.Builder<Integer> terms = ImmutableList.builder();
    for (int i = 0; i < Terms.numChildren(parent); i++) {
      SumComponent<?> component = Terms.projSum(parent, i);
      var factor = toConstant(component.getFactor());
      var term =
          component.getTerm() == Terms.NULL_TERM
              ? mkOne(Terms.typeOf(parent))
              : component.getTerm();

      terms.add(mkMultiply(factor, term));
    }
    return terms.build();
  }

  /**
   * Returns coefficient and term for a sum with only a single term.
   *
   * <p>Splits the sum term <code>Σ a*t</code> into <code>a</code> and <code>t</code>
   */
  private static List<Integer> getOnlySumTerm(int parent) {
    checkArgument(Terms.numChildren(parent) == 1);
    SumComponent<?> component = Terms.projSum(parent, 0);
    checkArgument(component.getTerm() != Terms.NULL_TERM);
    return ImmutableList.of(toConstant(component.getFactor()), component.getTerm());
  }

  /**
   * Returns a list of factors for a product term.
   *
   * <p>Splits a product <code>a^m * b^n * ...</code> into a list of monomials <code>a^m</code>,
   * <code>b^n</code>, ...
   */
  private static List<Integer> getProductFactors(int parent) {
    ImmutableList.Builder<Integer> builder = ImmutableList.builder();
    for (int i = 0; i < Terms.numChildren(parent); i++) {
      ProductComponent component = Terms.projProduct(parent, i);
      builder.add(mkPower(component.getTerm(), component.getPower()));
    }
    return builder.build();
  }

  @Override
  public Integer callFunctionImpl(Integer pDeclaration, List<Integer> pArgs) {
    if (Terms.isFunction(pDeclaration)) {
      checkArgument(
          Types.numChildren(Terms.typeOf(pDeclaration)) == 1 + pArgs.size(),
          "Expecting %s arguments, but found %s",
          Types.numChildren(Terms.typeOf(pDeclaration)) - 1,
          pArgs.size());
      return Terms.funApplication(pDeclaration, Ints.toArray(pArgs));
    } else {
      checkArgument(pArgs.isEmpty(), "Expecting no arguments, but found %s", pArgs.size());
      return pDeclaration;
    }
  }

  @Override
  public Integer declareUFImpl(String pName, Integer pReturnType, List<Integer> pArgTypes) {
    int[] argTypeArray = Ints.toArray(pArgTypes);
    final int yicesFuncType;
    if (pArgTypes.isEmpty()) {
      // a nullary function is a plain symbol (variable)
      yicesFuncType = pReturnType;
    } else {
      yicesFuncType = Types.functionType(argTypeArray, pReturnType);
    }
    int uf = createNamedVariable(yicesFuncType, pName);
    ufSymbols.add(uf);
    return uf;
  }

  @Override
  protected Integer getBooleanVarDeclarationImpl(Integer pTFormulaInfo) {
    return pTFormulaInfo;
  }

  private Object parseNumeralValue(Integer pF, FormulaType<?> type) {
    checkArgument(
        Terms.isArithConstant(pF),
        "Term: '%s' with type '%s' is not an arithmetic constant",
        Terms.toString(pF),
        Types.toString(Terms.typeOf(pF)));

    if (type.isRationalType()) {
      var rational = Terms.arithConstValue(pF);
      return rational.isInteger()
          ? rational.getNumerator()
          : Rational.of(rational.getNumerator(), rational.getDenominator());
    } else if (type.isIntegerType()) {
      return Terms.arithConstValue(pF).getNumerator();
    } else {
      throw new IllegalArgumentException("Unexpected type: " + type);
    }
  }

  /**
   * Converts an array of booleans into a BigInteger value.
   *
   * <p>Assumes "little endian" encoding
   */
  static BigInteger bitsToInteger(boolean[] bits) {
    // FIXME We're treating the bv as unsigned. Should we return a signed value instead?
    var value = BigInteger.ZERO;
    for (var p = 0; p < bits.length; p++) {
      if (bits[p]) {
        value = value.setBit(p);
      }
    }
    return value;
  }

  /**
   * Converts a BigInteger into an array of booleans.
   *
   * <p>Inverse of {@link #bitsToInteger}
   */
  static boolean[] integerToBits(int bitsize, BigInteger value) {
    checkArgument(bitsize >= value.bitLength());

    var bits = new boolean[bitsize];
    for (int p = 0; p < value.bitLength(); p++) {
      bits[p] = value.testBit(p);
    }
    return bits;
  }

  private BigInteger parseBitvector(int pF) {
    checkArgument(
        Terms.isBvConstant(pF), "Term: '%s' is not a bitvector constant", Terms.toString(pF));
    return bitsToInteger(Terms.bvConstValue(pF));
  }

  public boolean isArrayVariable(int term) {
    checkArgument(Terms.isFunction(term));
    checkArgument(Terms.isUninterpreted(term));
    return !ufSymbols.contains(term);
  }

  @Override
  public Object convertValue(Integer typeKey, Integer pF) {
    FormulaType<?> type = getFormulaType(typeKey);
    if (type.isBooleanType()) {
      return pF.equals(Terms.mkTrue());
    } else if (type.isRationalType() || type.isIntegerType()) {
      return parseNumeralValue(pF, type);
    } else if (type.isBitvectorType()) {
      return parseBitvector(pF);
    } else {
      throw new IllegalArgumentException("Unexpected type: " + Types.toString(Terms.typeOf(pF)));
    }
  }
}
