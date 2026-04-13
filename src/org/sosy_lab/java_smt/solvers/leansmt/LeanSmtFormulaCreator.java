// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;

final class LeanSmtFormulaCreator
    extends FormulaCreator<Long, LeanSmtType, Long, LeanSmtFunctionDecl> {

  private static final String MANGLED_IDENTIFIER_PREFIX = "__javasmt_escaped_";
  private static final String SIMPLE_NATIVE_IDENTIFIER_PATTERN =
      "[a-zA-Z~!@$%^&*_+=<>.?/-][a-zA-Z0-9~!@$%^&*_+=<>.?/-]*";
  private static final ImmutableSet<String> RESERVED_IDENTIFIERS =
      ImmutableSet.of(
          "true",
          "false",
          "and",
          "or",
          "select",
          "store",
          "xor",
          "distinct",
          "let",
          "forall",
          "exists",
          "match",
          "Bool",
          "continued-execution",
          "error",
          "immediate-exit",
          "incomplete",
          "logic",
          "memout",
          "sat",
          "success",
          "theory",
          "unknown",
          "unsupported",
          "unsat",
          "_",
          "as",
          "BINARY",
          "DECIMAL",
          "HEXADECIMAL",
          "NUMERAL",
          "par",
          "STRING",
          "assert",
          "check-sat",
          "check-sat-assuming",
          "declare-const",
          "declare-datatype",
          "declare-datatypes",
          "declare-fun",
          "declare-sort",
          "define-fun",
          "define-fun-rec",
          "define-sort",
          "echo",
          "exit",
          "get-assertions",
          "get-assignment",
          "get-info",
          "get-model",
          "get-option",
          "get-proof",
          "get-unsat-assumptions",
          "get-unsat-core",
          "get-value",
          "pop",
          "push",
          "reset",
          "reset-assertions",
          "set-info",
          "set-logic",
          "set-option");

  enum ExprKind {
    VARIABLE,
    CONSTANT,
    APPLICATION
  }

  static final class Expr {
    final ExprKind kind;
    final FormulaType<?> type;
    final String symbol;
    final @Nullable Object constantValue;
    final FunctionDeclarationKind declarationKind;
    final ImmutableList<Long> arguments;

    private Expr(
        ExprKind pKind,
        FormulaType<?> pType,
        String pSymbol,
        @Nullable Object pConstantValue,
        FunctionDeclarationKind pDeclarationKind,
        ImmutableList<Long> pArguments) {
      kind = pKind;
      type = pType;
      symbol = pSymbol;
      constantValue = pConstantValue;
      declarationKind = pDeclarationKind;
      arguments = pArguments;
    }
  }

  private final Map<Long, Expr> expressions = new ConcurrentHashMap<>();
  private final Map<String, LeanSmtType> declaredVariables = new LinkedHashMap<>();
  private final Map<String, Long> latestVariableHandles = new LinkedHashMap<>();
  private final Map<String, LeanSmtFunctionDecl> declaredUfDeclarations = new LinkedHashMap<>();
  private final Map<BigInteger, Long> intConstantHandles = new HashMap<>();
  private final Map<Rational, Long> realConstantHandles = new HashMap<>();
  private final Map<BitvectorConstantKey, Long> bitvectorConstantHandles = new HashMap<>();
  private final Map<OperationKey, Long> canonicalApplications = new HashMap<>();
  private final Map<ApplicationKey, Long> ufApplications = new HashMap<>();
  private long nextExpressionHandle = 1L;
  private final long trueHandle;
  private final long falseHandle;

  LeanSmtFormulaCreator() {
    super(0L, LeanSmtType.BOOL, LeanSmtType.INT, LeanSmtType.REAL, null, null);
    trueHandle = allocateExpressionHandle();
    falseHandle = allocateExpressionHandle();
    registerConstant(trueHandle, FormulaType.BooleanType, true);
    registerConstant(falseHandle, FormulaType.BooleanType, false);
  }

  private synchronized long allocateExpressionHandle() {
    return nextExpressionHandle++;
  }

  @Override
  public LeanSmtType getBitvectorType(int bitwidth) {
    return LeanSmtType.bitvector(bitwidth);
  }

  @Override
  public LeanSmtType getFloatingPointType(FormulaType.FloatingPointType type) {
    throw new UnsupportedOperationException("LeanSMT backend does not support floating points");
  }

  @Override
  public LeanSmtType getArrayType(LeanSmtType indexType, LeanSmtType elementType) {
    throw new UnsupportedOperationException("LeanSMT backend does not support arrays");
  }

  @Override
  public Long makeVariable(LeanSmtType type, String varName) {
    synchronized (this) {
      LeanSmtType existingType = declaredVariables.get(varName);
      if (existingType != null) {
        if (!existingType.equals(type)) {
          throw new IllegalArgumentException(
              "Conflicting declaration for variable '"
                  + varName
                  + "': existing type "
                  + existingType
                  + ", new type "
                  + type);
        }
        Long existingHandle = latestVariableHandles.get(varName);
        if (existingHandle != null) {
          return existingHandle;
        }
      }

      long handle = allocateExpressionHandle();
      registerVariable(handle, varName, type);
      return handle;
    }
  }

  synchronized void redeclareVariables(long solver, Set<String> variableNames)
      throws org.sosy_lab.java_smt.api.SolverException {
    for (String name : variableNames) {
      LeanSmtType type = declaredVariables.get(name);
      if (type == null) {
        throw new IllegalArgumentException("Unknown LeanSMT variable '" + name + "'");
      }
      LeanSmtNativeApi.declareFun(solver, encodeNativeIdentifier(name), "", toSmtLibSort(type));
    }
  }

  synchronized void redeclareUfDeclarations(long solver, Set<String> ufNames)
      throws org.sosy_lab.java_smt.api.SolverException {
    for (String name : ufNames) {
      LeanSmtFunctionDecl declaration = declaredUfDeclarations.get(name);
      if (declaration == null) {
        throw new IllegalArgumentException("Unknown LeanSMT UF '" + name + "'");
      }
      LeanSmtNativeApi.declareFun(
          solver,
          encodeNativeIdentifier(name),
          joinArgSorts(declaration.getArgumentTypes()),
          toSmtLibSort(declaration.getReturnType()));
    }
  }

  long getTrueHandle() {
    return trueHandle;
  }

  long getFalseHandle() {
    return falseHandle;
  }

  long makeIntConstant(long value) {
    return makeIntConstant(BigInteger.valueOf(value));
  }

  long makeIntConstant(BigInteger value) {
    synchronized (intConstantHandles) {
      Long existing = intConstantHandles.get(value);
      if (existing != null) {
        return existing;
      }
      long handle = allocateExpressionHandle();
      registerConstant(handle, FormulaType.IntegerType, value);
      intConstantHandles.put(value, handle);
      return handle;
    }
  }

  long makeRealConstant(long num, long den) {
    return makeRealConstant(Rational.of(BigInteger.valueOf(num), BigInteger.valueOf(den)));
  }

  long makeRealConstant(Rational value) {
    synchronized (realConstantHandles) {
      Long existing = realConstantHandles.get(value);
      if (existing != null) {
        return existing;
      }
      long handle = allocateExpressionHandle();
      registerConstant(handle, FormulaType.RationalType, value);
      realConstantHandles.put(value, handle);
      return handle;
    }
  }

  long makeBitvectorConstant(int bitwidth, BigInteger unsignedValue) {
    Preconditions.checkArgument(bitwidth > 0, "Bitvector size must be positive");
    Preconditions.checkArgument(
        unsignedValue.signum() >= 0, "Bitvector constant must be unsigned, got %s", unsignedValue);
    BigInteger modulus = BigInteger.ONE.shiftLeft(bitwidth);
    Preconditions.checkArgument(
        unsignedValue.compareTo(modulus) < 0,
        "Bitvector constant %s does not fit in %s bits",
        unsignedValue,
        bitwidth);

    BitvectorConstantKey key = new BitvectorConstantKey(bitwidth, unsignedValue);
    synchronized (bitvectorConstantHandles) {
      Long existing = bitvectorConstantHandles.get(key);
      if (existing != null) {
        return existing;
      }
      long handle = allocateExpressionHandle();
      registerConstant(handle, FormulaType.getBitvectorTypeWithSize(bitwidth), unsignedValue);
      bitvectorConstantHandles.put(key, handle);
      return handle;
    }
  }

  long makeUnary(String symbol, FunctionDeclarationKind kind, FormulaType<?> type, long arg) {
    ImmutableList<Long> arguments = ImmutableList.of(arg);
    OperationKey key = new OperationKey(symbol, kind, type, arguments);
    synchronized (canonicalApplications) {
      Long existing = canonicalApplications.get(key);
      if (existing != null) {
        return existing;
      }
      long handle = allocateExpressionHandle();
      registerApplication(handle, symbol, kind, type, arguments);
      canonicalApplications.put(key, handle);
      return handle;
    }
  }

  long makeBinary(
      String symbol, FunctionDeclarationKind kind, FormulaType<?> type, long arg1, long arg2) {
    Long trivialResult = simplifyBinaryWithIdenticalArguments(kind, arg1, arg2);
    if (trivialResult != null) {
      return trivialResult;
    }
    ImmutableList<Long> arguments = ImmutableList.of(arg1, arg2);
    OperationKey key = new OperationKey(symbol, kind, type, arguments);
    synchronized (canonicalApplications) {
      Long existing = canonicalApplications.get(key);
      if (existing != null) {
        return existing;
      }
      long handle = allocateExpressionHandle();
      registerApplication(handle, symbol, kind, type, arguments);
      canonicalApplications.put(key, handle);
      return handle;
    }
  }

  private @Nullable Long simplifyBinaryWithIdenticalArguments(
      FunctionDeclarationKind kind, long arg1, long arg2) {
    if (arg1 != arg2) {
      return null;
    }

    switch (kind) {
      case EQ:
      case IFF:
      case IMPLIES:
      case LTE:
      case GTE:
      case BV_EQ:
        return getTrueHandle();
      case DISTINCT:
      case XOR:
      case LT:
      case GT:
      case BV_ULT:
      case BV_SLT:
      case BV_UGT:
      case BV_SGT:
        return getFalseHandle();
      default:
        return null;
    }
  }

  long makeTernary(
      String symbol,
      FunctionDeclarationKind kind,
      FormulaType<?> type,
      long arg1,
      long arg2,
      long arg3) {
    ImmutableList<Long> arguments = ImmutableList.of(arg1, arg2, arg3);
    OperationKey key = new OperationKey(symbol, kind, type, arguments);
    synchronized (canonicalApplications) {
      Long existing = canonicalApplications.get(key);
      if (existing != null) {
        return existing;
      }
      long handle = allocateExpressionHandle();
      registerApplication(handle, symbol, kind, type, arguments);
      canonicalApplications.put(key, handle);
      return handle;
    }
  }

  Expr getExpression(long handle) {
    Expr expr = expressions.get(handle);
    Preconditions.checkArgument(expr != null, "Unknown LeanSMT term handle: %s", handle);
    return expr;
  }

  @Override
  public FormulaType<?> getFormulaType(Long formula) {
    return getExpression(formula).type;
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    if (formula instanceof BitvectorFormula) {
      FormulaType<?> type = getFormulaType(extractInfo(formula));
      Preconditions.checkArgument(
          type.isBitvectorType(), "BitvectorFormula with actual type %s: %s", type, formula);
      return (FormulaType<T>) type;
    }
    return super.getFormulaType(formula);
  }

  @Override
  public @Nullable Object convertValue(Long formula) {
    Expr expr = expressions.get(formula);
    if (expr == null || expr.constantValue == null) {
      return null;
    }
    if (expr.constantValue instanceof Rational) {
      Rational rational = (Rational) expr.constantValue;
      if (rational.getDen().equals(BigInteger.ONE)) {
        return rational.getNum();
      }
    }
    if (expr.constantValue instanceof Boolean
        || expr.constantValue instanceof BigInteger
        || expr.constantValue instanceof Rational) {
      return expr.constantValue;
    }
    return null;
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, Long handle) {
    Expr expr = getExpression(handle);
    switch (expr.kind) {
      case VARIABLE:
        return visitor.visitFreeVariable(formula, expr.symbol);

      case CONSTANT:
        return visitor.visitConstant(formula, normalizeConstantForVisitor(expr.constantValue));

      case APPLICATION:
        ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();
        List<Formula> args = new ArrayList<>(expr.arguments.size());
        for (long arg : expr.arguments) {
          FormulaType<?> argType = getFormulaType(arg);
          argTypes.add(argType);
          args.add(encapsulate(argType, arg));
        }
        LeanSmtFunctionDecl decl =
            new LeanSmtFunctionDecl(
                expr.symbol,
                expr.declarationKind,
                fromFormulaType(expr.type),
                expr.arguments.stream()
                    .map(this::getFormulaType)
                    .map(LeanSmtFormulaCreator::fromFormulaType)
                    .collect(ImmutableList.toImmutableList()));
        return visitor.visitFunction(
            formula,
            args,
            FunctionDeclarationImpl.of(
                expr.symbol,
                expr.declarationKind,
                argTypes.build(),
                castFormulaType(expr.type),
                decl));

      default:
        throw new AssertionError("Unexpected expression kind " + expr.kind);
    }
  }

  @Override
  public Long callFunctionImpl(LeanSmtFunctionDecl declaration, List<Long> args) {
    if (declaration.getKind() != FunctionDeclarationKind.UF) {
      return callBuiltInFunction(declaration, args);
    }

    if (args.isEmpty()) {
      return makeVariable(declaration.getReturnType(), declaration.getName());
    }

    synchronized (ufApplications) {
      ImmutableList<Long> normalizedArgs = castArgumentsToParameterTypes(declaration, args);
      ApplicationKey key = new ApplicationKey(declaration, normalizedArgs);
      Long existing = ufApplications.get(key);
      if (existing != null) {
        return existing;
      }

      long handle = allocateExpressionHandle();
      registerApplication(
          handle,
          declaration.getName(),
          FunctionDeclarationKind.UF,
          declaration.getReturnType().toFormulaType(),
          normalizedArgs);
      ufApplications.put(key, handle);
      return handle;
    }
  }

  @Override
  public LeanSmtFunctionDecl declareUFImpl(
      String name, LeanSmtType returnType, List<LeanSmtType> argTypes) {
    synchronized (this) {
      LeanSmtFunctionDecl declaration =
          new LeanSmtFunctionDecl(
              name, FunctionDeclarationKind.UF, returnType, ImmutableList.copyOf(argTypes));
      LeanSmtFunctionDecl existing = declaredUfDeclarations.get(name);
      if (existing == null) {
        declaredUfDeclarations.put(name, declaration);
        return declaration;
      }
      if (!existing.equals(declaration)) {
        throw new IllegalArgumentException(
            "Conflicting declaration for UF '"
                + name
                + "': existing return type "
                + existing.getReturnType()
                + " with arguments "
                + existing.getArgumentTypes()
                + ", new return type "
                + declaration.getReturnType()
                + " with arguments "
                + declaration.getArgumentTypes());
      }
      return existing;
    }
  }

  @Override
  protected LeanSmtFunctionDecl getBooleanVarDeclarationImpl(Long formulaInfo) {
    Expr expr = getExpression(formulaInfo);
    if (expr.kind != ExprKind.VARIABLE || !FormulaType.BooleanType.equals(expr.type)) {
      throw new UnsupportedOperationException(
          "LeanSMT term is not a declared Boolean variable: " + formulaInfo);
    }
    return new LeanSmtFunctionDecl(
        expr.symbol, FunctionDeclarationKind.VAR, LeanSmtType.BOOL, ImmutableList.of());
  }

  private synchronized void registerVariable(long handle, String name, LeanSmtType type) {
    declaredVariables.put(name, type);
    latestVariableHandles.put(name, handle);
    expressions.put(
        handle,
        new Expr(
            ExprKind.VARIABLE,
            type.toFormulaType(),
            name,
            null,
            FunctionDeclarationKind.VAR,
            ImmutableList.of()));
  }

  private void registerConstant(long handle, FormulaType<?> type, Object value) {
    expressions.put(
        handle,
        new Expr(
            ExprKind.CONSTANT,
            type,
            value.toString(),
            value,
            FunctionDeclarationKind.CONST,
            ImmutableList.of()));
  }

  private void registerApplication(
      long handle,
      String symbol,
      FunctionDeclarationKind kind,
      FormulaType<?> type,
      ImmutableList<Long> arguments) {
    expressions.put(handle, new Expr(ExprKind.APPLICATION, type, symbol, null, kind, arguments));
  }

  static String encodeIdentifier(String id) {
    if (!id.isEmpty()
        && (id.startsWith("@") || id.startsWith(".") || RESERVED_IDENTIFIERS.contains(id))) {
      return "|" + MANGLED_IDENTIFIER_PREFIX + toHexUtf8(id) + "|";
    }
    if (!id.isEmpty()
        && !id.startsWith("@")
        && !id.startsWith(".")
        && !id.startsWith(":")
        && !RESERVED_IDENTIFIERS.contains(id)
        && id.matches("[a-zA-Z~!@$%^&*_+=<>.?/-][a-zA-Z0-9~!@$%^&*_+=<>.?/-]*")) {
      return id;
    }
    return "|" + id.replace("|", "||") + "|";
  }

  static String encodeNativeIdentifier(String id) {
    if (isSimpleNativeIdentifier(id)) {
      return id;
    }
    return MANGLED_IDENTIFIER_PREFIX + toHexUtf8(id);
  }

  private static boolean isSimpleNativeIdentifier(String id) {
    return !id.isEmpty()
        && !id.startsWith("@")
        && !id.startsWith(".")
        && !id.startsWith(":")
        && !id.startsWith(MANGLED_IDENTIFIER_PREFIX)
        && !RESERVED_IDENTIFIERS.contains(id)
        && id.matches(SIMPLE_NATIVE_IDENTIFIER_PATTERN);
  }

  private static String toHexUtf8(String value) {
    byte[] bytes = value.getBytes(StandardCharsets.UTF_8);
    StringBuilder out = new StringBuilder(bytes.length * 2);
    for (byte b : bytes) {
      out.append(Character.forDigit((b >>> 4) & 0xF, 16));
      out.append(Character.forDigit(b & 0xF, 16));
    }
    return out.toString();
  }

  private static String toSmtLibSort(LeanSmtType type) {
    if (type.isBool()) {
      return "Bool";
    } else if (type.isInt()) {
      return "Int";
    } else if (type.isReal()) {
      return "Real";
    } else if (type.isBitvector()) {
      return "(_ BitVec " + type.getBitvectorSize() + ")";
    }
    throw new AssertionError("Unexpected LeanSMT type " + type);
  }

  private static String joinArgSorts(List<LeanSmtType> argumentTypes) {
    return argumentTypes.stream()
        .map(LeanSmtFormulaCreator::toSmtLibSort)
        .collect(java.util.stream.Collectors.joining(" "));
  }

  private static Object normalizeConstantForVisitor(@Nullable Object value) {
    if (value instanceof Rational) {
      Rational rational = (Rational) value;
      if (rational.getDen().equals(BigInteger.ONE)) {
        return rational.getNum();
      }
    }
    return value;
  }

  private ImmutableList<Long> castArgumentsToParameterTypes(
      LeanSmtFunctionDecl declaration, List<Long> args) {
    ImmutableList.Builder<Long> normalizedArgs = ImmutableList.builderWithExpectedSize(args.size());
    List<LeanSmtType> parameterTypes = declaration.getArgumentTypes();
    for (int i = 0; i < args.size(); i++) {
      long arg = args.get(i);
      LeanSmtType expectedType = parameterTypes.get(i);
      if (expectedType.isReal() && FormulaType.IntegerType.equals(getFormulaType(arg))) {
        normalizedArgs.add(normalizeIntegerToRealArgument(arg));
      } else {
        normalizedArgs.add(arg);
      }
    }
    return normalizedArgs.build();
  }

  private long normalizeIntegerToRealArgument(long arg) {
    Expr expr = getExpression(arg);
    if (expr.kind == ExprKind.CONSTANT && expr.constantValue instanceof BigInteger) {
      BigInteger integerValue = (BigInteger) expr.constantValue;
      return makeRealConstant(Rational.of(integerValue, BigInteger.ONE));
    }
    return makeUnary("to_real", FunctionDeclarationKind.TO_REAL, FormulaType.RationalType, arg);
  }

  @SuppressWarnings("unchecked")
  private static <T extends Formula> FormulaType<T> castFormulaType(FormulaType<?> type) {
    return (FormulaType<T>) type;
  }

  static LeanSmtType fromFormulaType(FormulaType<?> type) {
    if (FormulaType.BooleanType.equals(type)) {
      return LeanSmtType.BOOL;
    } else if (FormulaType.IntegerType.equals(type)) {
      return LeanSmtType.INT;
    } else if (FormulaType.RationalType.equals(type)) {
      return LeanSmtType.REAL;
    } else if (type.isBitvectorType()) {
      return LeanSmtType.bitvector(((FormulaType.BitvectorType) type).getSize());
    }
    throw new UnsupportedOperationException("Unsupported formula type for LeanSMT: " + type);
  }

  Long extractInfoFromFormula(Formula formula) {
    return extractInfo(formula);
  }

  long makeFloorTerm(long argument) {
    return makeUnary("to_int", FunctionDeclarationKind.FLOOR, FormulaType.IntegerType, argument);
  }

  long makeIntToBitvectorTerm(int bitwidth, long integerTerm) {
    Preconditions.checkArgument(bitwidth > 0, "Bitvector size must be positive");
    return makeUnary(
        intToBvSymbol(bitwidth),
        FunctionDeclarationKind.INT_TO_BV,
        FormulaType.getBitvectorTypeWithSize(bitwidth),
        integerTerm);
  }

  private static String intToBvSymbol(int bitwidth) {
    return "(_ int_to_bv " + bitwidth + ")";
  }

  private long callBuiltInFunction(LeanSmtFunctionDecl declaration, List<Long> args) {
    FunctionDeclarationKind kind = declaration.getKind();
    FormulaType<?> returnType = declaration.getReturnType().toFormulaType();
    String symbol = declaration.getName();
    ImmutableList<Long> immutableArgs = ImmutableList.copyOf(args);
    OperationKey key = new OperationKey(symbol, kind, returnType, immutableArgs);
    synchronized (canonicalApplications) {
      Long existing = canonicalApplications.get(key);
      if (existing != null) {
        return existing;
      }
    }

    @Nullable Long handled =
        tryHandleCoreBuiltInFunction(declaration, args, kind, returnType, symbol);
    if (handled != null) {
      return handled;
    }

    handled = tryHandleBitvectorBuiltInFunction(declaration, args, kind, returnType, symbol);
    if (handled != null) {
      return handled;
    }

    throw new UnsupportedOperationException(
        "LeanSMT backend cannot rebuild function declaration kind " + kind);
  }

  private @Nullable Long tryHandleCoreBuiltInFunction(
      LeanSmtFunctionDecl declaration,
      List<Long> args,
      FunctionDeclarationKind kind,
      FormulaType<?> returnType,
      String symbol) {
    switch (kind) {
      case NOT:
        checkArity(declaration, args, 1);
        return makeUnary("not", kind, FormulaType.BooleanType, args.get(0));
      case AND:
        return foldAnd(args);
      case OR:
        return foldOr(args);
      case XOR:
        return foldLeft("xor", kind, FormulaType.BooleanType, args);
      case IMPLIES:
        return foldLeft("=>", kind, FormulaType.BooleanType, args);
      case ITE:
        checkArity(declaration, args, 3);
        return makeTernary("ite", kind, returnType, args.get(0), args.get(1), args.get(2));
      case EQ:
        return foldPairwiseBoolean("=", kind, args);
      case DISTINCT:
        return foldAllDistinct(args);
      case LT:
        return foldPairwiseBoolean("<", kind, args);
      case LTE:
        return foldPairwiseBoolean("<=", kind, args);
      case GT:
        return foldPairwiseBoolean(">", kind, args);
      case GTE:
        return foldPairwiseBoolean(">=", kind, args);
      case ADD:
        return foldLeft("+", kind, returnType, args);
      case SUB:
        if (args.size() == 1) {
          return makeUnary("-", FunctionDeclarationKind.UMINUS, returnType, args.get(0));
        }
        return foldLeft("-", kind, returnType, args);
      case MUL:
        return foldLeft("*", kind, returnType, args);
      case DIV:
        if (returnType.isRationalType()) {
          return foldLeft("/", kind, returnType, args);
        }
        return foldLeft("div", kind, returnType, args);
      case MODULO:
        return foldLeft("mod", kind, returnType, args);
      case UMINUS:
        checkArity(declaration, args, 1);
        return makeUnary("-", kind, returnType, args.get(0));
      case TO_REAL:
        checkArity(declaration, args, 1);
        return makeUnary("to_real", kind, FormulaType.RationalType, args.get(0));
      case FLOOR:
        checkArity(declaration, args, 1);
        return makeFloorTerm(args.get(0));
      case INT_TO_BV:
        checkArity(declaration, args, 1);
        return makeIntToBitvectorTerm(parseIntToBvWidth(declaration, returnType), args.get(0));
      case BV_EXTRACT:
        checkArity(declaration, args, 1);
        parseExtractIndices(symbol);
        return makeUnary(symbol, kind, returnType, args.get(0));
      case BV_SIGN_EXTENSION:
      case BV_ZERO_EXTENSION:
        checkArity(declaration, args, 1);
        String extendOp =
            kind == FunctionDeclarationKind.BV_SIGN_EXTENSION ? "sign_extend" : "zero_extend";
        parseIndexedUnaryParameter(symbol, extendOp);
        return makeUnary(symbol, kind, returnType, args.get(0));
      case BV_ROTATE_LEFT_BY_INT:
      case BV_ROTATE_RIGHT_BY_INT:
        checkArity(declaration, args, 1);
        String rotateByIntOp =
            kind == FunctionDeclarationKind.BV_ROTATE_LEFT_BY_INT ? "rotate_left" : "rotate_right";
        parseIndexedUnaryParameter(symbol, rotateByIntOp);
        return makeUnary(symbol, kind, returnType, args.get(0));
      case BV_NOT:
      case BV_NEG:
      case UBV_TO_INT:
        checkArity(declaration, args, 1);
        return makeUnary(symbol, kind, returnType, args.get(0));
      case SBV_TO_INT:
        checkArity(declaration, args, 1);
        return makeSignedBitvectorToIntegerTerm(args.get(0));
      default:
        return null;
    }
  }

  private @Nullable Long tryHandleBitvectorBuiltInFunction(
      LeanSmtFunctionDecl declaration,
      List<Long> args,
      FunctionDeclarationKind kind,
      FormulaType<?> returnType,
      String symbol) {
    switch (kind) {
      case BV_CONCAT:
      case BV_AND:
      case BV_OR:
      case BV_XOR:
      case BV_ADD:
      case BV_SUB:
      case BV_MUL:
      case BV_UDIV:
      case BV_SDIV:
      case BV_UREM:
      case BV_SREM:
      case BV_SMOD:
      case BV_SHL:
      case BV_LSHR:
      case BV_ASHR:
      case BV_ROTATE_LEFT:
      case BV_ROTATE_RIGHT:
        checkArity(declaration, args, 2);
        return makeBinary(symbol, kind, returnType, args.get(0), args.get(1));
      case BV_EQ:
        return foldPairwiseBoolean("=", kind, args);
      case BV_ULT:
      case BV_ULE:
      case BV_UGT:
      case BV_UGE:
      case BV_SLT:
      case BV_SLE:
      case BV_SGT:
      case BV_SGE:
        checkArity(declaration, args, 2);
        return makeBinary(symbol, kind, FormulaType.BooleanType, args.get(0), args.get(1));
      default:
        return null;
    }
  }

  long makeSignedBitvectorToIntegerTerm(long bitvectorTerm) {
    return makeUnary(
        "sbv_to_int", FunctionDeclarationKind.SBV_TO_INT, FormulaType.IntegerType, bitvectorTerm);
  }

  private static int parseIntToBvWidth(LeanSmtFunctionDecl declaration, FormulaType<?> returnType) {
    String symbol = declaration.getName();
    if (symbol.startsWith("(_ int_to_bv ")) {
      return parseIndexedUnaryParameter(symbol, "int_to_bv");
    }
    if (symbol.startsWith("(_ int2bv ")) {
      return parseIndexedUnaryParameter(symbol, "int2bv");
    }
    if (returnType.isBitvectorType()) {
      return ((FormulaType.BitvectorType) returnType).getSize();
    }
    throw new IllegalArgumentException(
        "Cannot infer int-to-bv width from declaration symbol '" + symbol + "'");
  }

  private static int parseIndexedUnaryParameter(String symbol, String expectedOp) {
    String[] parts = tokenizeIndexedSymbol(symbol);
    if (parts.length != 3 || !"_".equals(parts[0]) || !expectedOp.equals(parts[1])) {
      throw new IllegalArgumentException(
          "Expected indexed symbol '(_ " + expectedOp + " k)', got '" + symbol + "'");
    }
    return parseNonNegativeIndex(parts[2], symbol);
  }

  private static int[] parseExtractIndices(String symbol) {
    String[] parts = tokenizeIndexedSymbol(symbol);
    if (parts.length != 4 || !"_".equals(parts[0]) || !"extract".equals(parts[1])) {
      throw new IllegalArgumentException(
          "Expected indexed symbol '(_ extract msb lsb)', got '" + symbol + "'");
    }
    int msb = parseNonNegativeIndex(parts[2], symbol);
    int lsb = parseNonNegativeIndex(parts[3], symbol);
    if (msb < lsb) {
      throw new IllegalArgumentException("Expected extract with msb >= lsb, got '" + symbol + "'");
    }
    return new int[] {msb, lsb};
  }

  private static String[] tokenizeIndexedSymbol(String symbol) {
    String trimmed = symbol.trim();
    if (!trimmed.startsWith("(_ ") || !trimmed.endsWith(")")) {
      throw new IllegalArgumentException("Malformed indexed symbol '" + symbol + "'");
    }
    String body = trimmed.substring(1, trimmed.length() - 1).trim();
    return body.split("\\s+");
  }

  private static int parseNonNegativeIndex(String token, String fullSymbol) {
    try {
      int value = Integer.parseInt(token);
      if (value < 0) {
        throw new IllegalArgumentException(
            "Indexed symbol must use non-negative indices: '" + fullSymbol + "'");
      }
      return value;
    } catch (NumberFormatException e) {
      throw new IllegalArgumentException(
          "Indexed symbol contains invalid index in '" + fullSymbol + "'", e);
    }
  }

  private long foldAnd(List<Long> args) {
    if (args.isEmpty()) {
      return getTrueHandle();
    }
    long result = args.get(0);
    for (int i = 1; i < args.size(); i++) {
      result =
          makeBinary(
              "and", FunctionDeclarationKind.AND, FormulaType.BooleanType, result, args.get(i));
    }
    return result;
  }

  private long foldOr(List<Long> args) {
    if (args.isEmpty()) {
      return getFalseHandle();
    }
    long result = args.get(0);
    for (int i = 1; i < args.size(); i++) {
      result =
          makeBinary(
              "or", FunctionDeclarationKind.OR, FormulaType.BooleanType, result, args.get(i));
    }
    return result;
  }

  private long foldLeft(
      String symbol, FunctionDeclarationKind kind, FormulaType<?> type, List<Long> args) {
    if (args.isEmpty()) {
      throw new IllegalArgumentException("Cannot apply " + kind + " to empty argument list");
    }
    long result = args.get(0);
    for (int i = 1; i < args.size(); i++) {
      result = makeBinary(symbol, kind, type, result, args.get(i));
    }
    return result;
  }

  private long foldPairwiseBoolean(String symbol, FunctionDeclarationKind kind, List<Long> args) {
    if (args.size() < 2) {
      return getTrueHandle();
    }
    long result = makeBinary(symbol, kind, FormulaType.BooleanType, args.get(0), args.get(1));
    for (int i = 2; i < args.size(); i++) {
      long next = makeBinary(symbol, kind, FormulaType.BooleanType, args.get(i - 1), args.get(i));
      result =
          makeBinary("and", FunctionDeclarationKind.AND, FormulaType.BooleanType, result, next);
    }
    return result;
  }

  private long foldAllDistinct(List<Long> args) {
    if (args.size() < 2) {
      return getTrueHandle();
    }
    Long result = null;
    for (int i = 0; i < args.size(); i++) {
      for (int j = i + 1; j < args.size(); j++) {
        long neq =
            makeBinary(
                "distinct",
                FunctionDeclarationKind.DISTINCT,
                FormulaType.BooleanType,
                args.get(i),
                args.get(j));
        if (result == null) {
          result = neq;
        } else {
          result =
              makeBinary("and", FunctionDeclarationKind.AND, FormulaType.BooleanType, result, neq);
        }
      }
    }
    return Preconditions.checkNotNull(result);
  }

  private static void checkArity(LeanSmtFunctionDecl declaration, List<Long> args, int expected) {
    if (args.size() != expected) {
      throw new IllegalArgumentException(
          "Unexpected arity for "
              + declaration.getKind()
              + " '"
              + declaration.getName()
              + "': expected "
              + expected
              + " but got "
              + args.size());
    }
  }

  private static final class BitvectorConstantKey {
    private final int size;
    private final BigInteger value;

    BitvectorConstantKey(int pSize, BigInteger pValue) {
      size = pSize;
      value = pValue;
    }

    @Override
    public boolean equals(Object other) {
      if (this == other) {
        return true;
      }
      if (!(other instanceof BitvectorConstantKey)) {
        return false;
      }
      BitvectorConstantKey that = (BitvectorConstantKey) other;
      return size == that.size && value.equals(that.value);
    }

    @Override
    public int hashCode() {
      return Objects.hash(size, value);
    }
  }

  private static final class ApplicationKey {
    private final LeanSmtFunctionDecl declaration;
    private final ImmutableList<Long> args;

    ApplicationKey(LeanSmtFunctionDecl pDeclaration, ImmutableList<Long> pArgs) {
      declaration = pDeclaration;
      args = pArgs;
    }

    @Override
    public boolean equals(Object other) {
      if (this == other) {
        return true;
      }
      if (!(other instanceof ApplicationKey)) {
        return false;
      }
      ApplicationKey that = (ApplicationKey) other;
      return declaration.equals(that.declaration) && args.equals(that.args);
    }

    @Override
    public int hashCode() {
      return Objects.hash(declaration, args);
    }
  }

  private static final class OperationKey {
    private final String symbol;
    private final FunctionDeclarationKind kind;
    private final FormulaType<?> type;
    private final ImmutableList<Long> args;

    OperationKey(
        String pSymbol,
        FunctionDeclarationKind pKind,
        FormulaType<?> pType,
        ImmutableList<Long> pArgs) {
      symbol = pSymbol;
      kind = pKind;
      type = pType;
      args = pArgs;
    }

    @Override
    public boolean equals(Object other) {
      if (this == other) {
        return true;
      }
      if (!(other instanceof OperationKey)) {
        return false;
      }
      OperationKey that = (OperationKey) other;
      return symbol.equals(that.symbol)
          && kind == that.kind
          && type.equals(that.type)
          && args.equals(that.args);
    }

    @Override
    public int hashCode() {
      return Objects.hash(symbol, kind, type, args);
    }
  }
}
