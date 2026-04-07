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
import com.google.common.collect.ImmutableMap;
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
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;

final class LeanSmtFormulaCreator
    extends FormulaCreator<Long, LeanSmtType, Long, LeanSmtFunctionDecl> {
  // Keep chunks comfortably within 32-bit signed range for robust native interop.
  private static final BigInteger INT_CHUNK_BASE = BigInteger.TEN.pow(9);
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
    final Object constantValue;
    final FunctionDeclarationKind declarationKind;
    final ImmutableList<Long> arguments;

    private Expr(
        ExprKind pKind,
        FormulaType<?> pType,
        String pSymbol,
        Object pConstantValue,
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

  private static final class FlattenedApplication {
    private final String symbol;
    private final ImmutableList<Long> arguments;

    private FlattenedApplication(String pSymbol, ImmutableList<Long> pArguments) {
      symbol = pSymbol;
      arguments = pArguments;
    }
  }

  private final Map<Long, FormulaType<?>> formulaTypes = new ConcurrentHashMap<>();
  private final Map<Long, Object> constantValues = new ConcurrentHashMap<>();
  private final Map<Long, FunctionDeclarationKind> declarationKinds = new ConcurrentHashMap<>();
  private final Map<String, LeanSmtType> declaredVariables = new LinkedHashMap<>();
  private final Map<String, Long> latestVariableHandles = new LinkedHashMap<>();
  private final Map<String, LeanSmtFunctionDecl> declaredUfDeclarations = new LinkedHashMap<>();
  private final Map<BigInteger, Long> intConstantHandles = new HashMap<>();
  private final Map<Rational, Long> realConstantHandles = new HashMap<>();
  private final Map<BitvectorConstantKey, Long> bitvectorConstantHandles = new HashMap<>();
  private final Map<OperationKey, Long> canonicalApplications = new HashMap<>();
  private final Map<ApplicationKey, Long> ufApplications = new HashMap<>();
  private final long trueHandle;
  private final long falseHandle;

  LeanSmtFormulaCreator() {
    super(0L, LeanSmtType.BOOL, LeanSmtType.INT, LeanSmtType.REAL, null, null);
    try {
      trueHandle = LeanSmtNativeApi.mkTrue();
      falseHandle = LeanSmtNativeApi.mkFalse();
      registerConstant(trueHandle, FormulaType.BooleanType, true);
      registerConstant(falseHandle, FormulaType.BooleanType, false);
    } catch (Exception e) {
      throw new IllegalStateException("Failed to initialize LeanSMT constants", e);
    }
  }

  @Override
  public LeanSmtType getBitvectorType(int bitwidth) {
    return LeanSmtType.bitvector(bitwidth);
  }

  @Override
  public LeanSmtType getFloatingPointType(FormulaType.FloatingPointType type) {
    throw new UnsupportedOperationException("LeanSMT backend does not support floating points yet");
  }

  @Override
  public LeanSmtType getArrayType(LeanSmtType indexType, LeanSmtType elementType) {
    throw new UnsupportedOperationException("LeanSMT backend does not support arrays yet");
  }

  @Override
  public Long makeVariable(LeanSmtType type, String varName) {
    synchronized (this) {
      LeanSmtType existingType = declaredVariables.get(varName);
      if (existingType != null) {
        if (!existingType.equals(type)) {
          throw new IllegalArgumentException(
              "Conflicting declaration for variable '" + varName + "': existing type " + existingType + ", new type " + type);
        }
        Long existingHandle = latestVariableHandles.get(varName);
        if (existingHandle != null) {
          return existingHandle;
        }
      }

      try {
        if (!type.isBool() && !type.isInt() && !type.isReal() && !type.isBitvector()) {
          throw new AssertionError("Unexpected LeanSMT type " + type);
        }
        long handle = LeanSmtNativeApi.mkSymbol(encodeNativeIdentifier(varName));
        registerVariable(handle, varName, type);
        return handle;
      } catch (Exception e) {
        throw new IllegalArgumentException("Failed to create variable in LeanSMT: " + varName, e);
      }
    }
  }

  synchronized void redeclareVariables(long solver, Set<String> namesToDeclare) {
    for (String name : namesToDeclare) {
      LeanSmtType type = declaredVariables.get(name);
      if (type != null) {
        declareVariableOnSolver(solver, name, type);
      }
    }
  }

  synchronized ImmutableMap<String, LeanSmtType> getDeclaredVariableTypes() {
    return ImmutableMap.copyOf(declaredVariables);
  }

  List<LeanSmtFunctionDecl> getKnownUfDeclarations() {
    synchronized (declaredUfDeclarations) {
      return ImmutableList.copyOf(declaredUfDeclarations.values());
    }
  }

  synchronized void redeclareUfDeclarations(long solver, Set<String> namesToDeclare)
      throws org.sosy_lab.java_smt.api.SolverException {
    for (String name : namesToDeclare) {
      LeanSmtFunctionDecl declaration = declaredUfDeclarations.get(name);
      if (declaration == null || declaration.getArgumentTypes().isEmpty()) {
        continue;
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
      try {
        long handle;
        if (fitsInLong(value) && value.signum() >= 0) {
          handle = LeanSmtNativeApi.mkIntConst(value.longValue());
        } else {
          handle = buildBigIntegerTerm(value);
        }
        registerConstant(handle, FormulaType.IntegerType, value);
        intConstantHandles.put(value, handle);
        return handle;
      } catch (Exception e) {
        throw new IllegalArgumentException("Failed to create integer constant", e);
      }
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
      try {
        long handle;
        BigInteger num = value.getNum();
        BigInteger den = value.getDen();
        if (den.equals(BigInteger.ONE)) {
          handle = buildBigRealFromNonNegativeInteger(num.abs());
          if (num.signum() < 0) {
            handle =
                makeUnary(
                    "-",
                    FunctionDeclarationKind.UMINUS,
                    FormulaType.RationalType,
                    handle,
                    LeanSmtNativeApi::mkNeg);
          }
        } else {
          handle = buildExactRationalTerm(value);
        }
        registerConstant(handle, FormulaType.RationalType, value);
        realConstantHandles.put(value, handle);
        return handle;
      } catch (Exception e) {
        throw new IllegalArgumentException("Failed to create rational constant", e);
      }
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
      try {
        long handle = LeanSmtNativeApi.mkBvConst(bitwidth, unsignedValue.toString());
        registerConstant(
            handle, FormulaType.getBitvectorTypeWithSize(bitwidth), unsignedValue);
        bitvectorConstantHandles.put(key, handle);
        return handle;
      } catch (Exception e) {
        throw new IllegalArgumentException(
            "Failed to create bitvector constant (width="
                + bitwidth
                + ", value="
                + unsignedValue
                + ")",
            e);
      }
    }
  }

  long makeUnary(
      String symbol, FunctionDeclarationKind kind, FormulaType<?> type, long arg, NativeUnary op) {
    ImmutableList<Long> arguments = ImmutableList.of(arg);
    OperationKey key = new OperationKey(symbol, kind, type, arguments);
    synchronized (canonicalApplications) {
      Long existing = canonicalApplications.get(key);
      if (existing != null) {
        return existing;
      }
      try {
        long handle = op.apply(arg);
        registerApplication(handle, kind, type);
        canonicalApplications.put(key, handle);
        return handle;
      } catch (Exception e) {
        throw new IllegalArgumentException("Failed to create term '" + symbol + "'", e);
      }
    }
  }

  long makeBinary(
      String symbol,
      FunctionDeclarationKind kind,
      FormulaType<?> type,
      long arg1,
      long arg2,
      NativeBinary op) {
    ImmutableList<Long> arguments = ImmutableList.of(arg1, arg2);
    OperationKey key = new OperationKey(symbol, kind, type, arguments);
    synchronized (canonicalApplications) {
      Long existing = canonicalApplications.get(key);
      if (existing != null) {
        return existing;
      }
      try {
        long handle = op.apply(arg1, arg2);
        registerApplication(handle, kind, type);
        canonicalApplications.put(key, handle);
        return handle;
      } catch (Exception e) {
        throw new IllegalArgumentException("Failed to create term '" + symbol + "'", e);
      }
    }
  }

  long makeTernary(
      String symbol,
      FunctionDeclarationKind kind,
      FormulaType<?> type,
      long arg1,
      long arg2,
      long arg3,
      NativeTernary op) {
    ImmutableList<Long> arguments = ImmutableList.of(arg1, arg2, arg3);
    OperationKey key = new OperationKey(symbol, kind, type, arguments);
    synchronized (canonicalApplications) {
      Long existing = canonicalApplications.get(key);
      if (existing != null) {
        return existing;
      }
      try {
        long handle = op.apply(arg1, arg2, arg3);
        registerApplication(handle, kind, type);
        canonicalApplications.put(key, handle);
        return handle;
      } catch (Exception e) {
        throw new IllegalArgumentException("Failed to create term '" + symbol + "'", e);
      }
    }
  }

  Expr getExpression(long handle) {
    FormulaType<?> type = formulaTypes.get(handle);
    Preconditions.checkArgument(type != null, "Unknown LeanSMT term handle: %s", handle);

    Object constantValue = constantValues.get(handle);
    if (constantValue != null) {
      return new Expr(
          ExprKind.CONSTANT,
          type,
          constantValue.toString(),
          constantValue,
          FunctionDeclarationKind.CONST,
          ImmutableList.of());
    }

    int nativeKind;
    try {
      nativeKind = LeanSmtNativeApi.getTermKind(handle);
    } catch (org.sosy_lab.java_smt.api.SolverException e) {
      throw new IllegalStateException("Failed to inspect LeanSMT term " + handle, e);
    }

    if (nativeKind == LeanSmtNativeApi.TERM_KIND_SYMBOL) {
      String rawSymbol = getNativeTermText(handle);
      String symbol = decodeNativeIdentifier(rawSymbol);
      Preconditions.checkArgument(
          declaredVariables.containsKey(symbol), "Unexpected LeanSMT symbol term: %s", rawSymbol);
      return new Expr(
          ExprKind.VARIABLE,
          type,
          symbol,
          null,
          FunctionDeclarationKind.VAR,
          ImmutableList.of());
    }

    if (nativeKind == LeanSmtNativeApi.TERM_KIND_APPLICATION) {
      FlattenedApplication application = flattenApplication(handle);
      FunctionDeclarationKind kind = declarationKinds.get(handle);
      Preconditions.checkArgument(
          kind != null, "Missing declaration kind for LeanSMT application handle: %s", handle);
      return new Expr(
          ExprKind.APPLICATION, type, application.symbol, null, kind, application.arguments);
    }

    if (nativeKind == LeanSmtNativeApi.TERM_KIND_LITERAL) {
      throw new IllegalStateException(
          "LeanSMT literal term without registered constant value: " + handle);
    }

    throw new IllegalStateException("Unexpected LeanSMT term kind " + nativeKind + " for " + handle);
  }

  @Override
  public FormulaType<?> getFormulaType(Long formula) {
    FormulaType<?> type = formulaTypes.get(formula);
    Preconditions.checkArgument(type != null, "Unknown LeanSMT term handle: %s", formula);
    return type;
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
    Object value = constantValues.get(formula);
    if (value == null) {
      return null;
    }
    if (value instanceof Rational) {
      Rational rational = (Rational) value;
      if (rational.getDen().equals(BigInteger.ONE)) {
        return rational.getNum();
      }
      return rational;
    }
    if (value instanceof Boolean || value instanceof BigInteger) {
      return value;
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
                expr.symbol, expr.declarationKind, argTypes.build(), castFormulaType(expr.type), decl));

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
      // Most JavaSMT backends model nullary UFs like named constants/variables. Reuse the same
      // symbol handle so equality, extraction, and visitor behavior line up with the shared suite.
      return makeVariable(declaration.getReturnType(), declaration.getName());
    }

    synchronized (ufApplications) {
      ImmutableList<Long> normalizedArgs = castArgumentsToParameterTypes(declaration, args);
      ApplicationKey key = new ApplicationKey(declaration, normalizedArgs);
      Long existing = ufApplications.get(key);
      if (existing != null) {
        return existing;
      }

      long handle = makeNativeApplication(declaration.getName(), key.args);
      registerApplication(
          handle, FunctionDeclarationKind.UF, declaration.getReturnType().toFormulaType());
      ufApplications.put(key, handle);
      return handle;
    }
  }

  @Override
  public LeanSmtFunctionDecl declareUFImpl(
      String name, LeanSmtType returnType, List<LeanSmtType> argTypes) {
    synchronized (declaredUfDeclarations) {
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
    formulaTypes.put(handle, type.toFormulaType());
  }

  private void declareVariableOnSolver(long solver, String name, LeanSmtType type) {
    try {
      if (!type.isBool() && !type.isInt() && !type.isReal() && !type.isBitvector()) {
        throw new AssertionError("Unexpected LeanSMT type " + type);
      }
      LeanSmtNativeApi.declareFun(solver, encodeNativeIdentifier(name), "", toSmtLibSort(type));
    } catch (Exception e) {
      throw new IllegalStateException("Failed to declare variable " + name, e);
    }
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

  static String decodeIdentifier(String token) {
    String id = token;
    boolean wasQuoted = false;
    if (token.length() >= 2 && token.startsWith("|") && token.endsWith("|")) {
      id = token.substring(1, token.length() - 1).replace("||", "|");
      wasQuoted = true;
    }
    if (wasQuoted && id.startsWith(MANGLED_IDENTIFIER_PREFIX)) {
      return fromHexUtf8(id.substring(MANGLED_IDENTIFIER_PREFIX.length()));
    }
    return id;
  }

  static String decodeNativeIdentifier(String token) {
    if (token.startsWith(MANGLED_IDENTIFIER_PREFIX)) {
      return fromHexUtf8(token.substring(MANGLED_IDENTIFIER_PREFIX.length()));
    }
    return token;
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

  private static String fromHexUtf8(String hex) {
    Preconditions.checkArgument(
        hex.length() % 2 == 0, "Malformed LeanSMT escaped identifier payload: %s", hex);
    byte[] bytes = new byte[hex.length() / 2];
    for (int i = 0; i < hex.length(); i += 2) {
      int high = Character.digit(hex.charAt(i), 16);
      int low = Character.digit(hex.charAt(i + 1), 16);
      Preconditions.checkArgument(
          high >= 0 && low >= 0, "Malformed LeanSMT escaped identifier payload: %s", hex);
      bytes[i / 2] = (byte) ((high << 4) | low);
    }
    return new String(bytes, StandardCharsets.UTF_8);
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

  private void registerConstant(long handle, FormulaType<?> type, Object value) {
    formulaTypes.put(handle, type);
    constantValues.put(handle, value);
  }

  private static Object normalizeConstantForVisitor(Object value) {
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
        normalizedArgs.add(
            makeUnary(
                "to_real",
                FunctionDeclarationKind.TO_REAL,
                FormulaType.RationalType,
                arg,
                t -> LeanSmtNativeApi.mkApp1("to_real", t)));
      } else {
        normalizedArgs.add(arg);
      }
    }
    return normalizedArgs.build();
  }

  private long makeNativeApplication(String symbol, ImmutableList<Long> arguments) {
    try {
      long app = LeanSmtNativeApi.mkSymbol(encodeNativeIdentifier(symbol));
      for (long argument : arguments) {
        app = LeanSmtNativeApi.mkApply(app, argument);
      }
      return app;
    } catch (Exception e) {
      throw new IllegalArgumentException("Failed to create LeanSMT application '" + symbol + "'", e);
    }
  }

  private String getNativeTermText(long handle) {
    try {
      return LeanSmtNativeApi.getTermText(handle);
    } catch (org.sosy_lab.java_smt.api.SolverException e) {
      throw new IllegalStateException("Failed to inspect LeanSMT term text for " + handle, e);
    }
  }

  private FlattenedApplication flattenApplication(long handle) {
    List<Long> reversedArguments = new ArrayList<>();
    long current = handle;
    while (true) {
      final int kind;
      final int childCount;
      try {
        kind = LeanSmtNativeApi.getTermKind(current);
        childCount = LeanSmtNativeApi.getTermNumChildren(current);
      } catch (org.sosy_lab.java_smt.api.SolverException e) {
        throw new IllegalStateException("Failed to inspect LeanSMT application " + handle, e);
      }

      if (kind != LeanSmtNativeApi.TERM_KIND_APPLICATION) {
        String symbol;
        if (kind == LeanSmtNativeApi.TERM_KIND_SYMBOL) {
          symbol = decodeNativeIdentifier(getNativeTermText(current));
        } else if (kind == LeanSmtNativeApi.TERM_KIND_LITERAL) {
          symbol = getNativeTermText(current);
        } else {
          throw new IllegalStateException(
              "Unexpected LeanSMT application head kind " + kind + " for " + handle);
        }
        java.util.Collections.reverse(reversedArguments);
        return new FlattenedApplication(symbol, ImmutableList.copyOf(reversedArguments));
      }

      Preconditions.checkState(
          childCount == 2,
          "LeanSMT applications are expected to be binary nodes, got %s children for %s",
          childCount,
          current);
      try {
        reversedArguments.add(LeanSmtNativeApi.getTermChild(current, 1));
        current = LeanSmtNativeApi.getTermChild(current, 0);
      } catch (org.sosy_lab.java_smt.api.SolverException e) {
        throw new IllegalStateException("Failed to inspect LeanSMT application children for " + handle, e);
      }
    }
  }

  private static boolean fitsInLong(BigInteger value) {
    return value.compareTo(BigInteger.valueOf(Long.MIN_VALUE)) >= 0
        && value.compareTo(BigInteger.valueOf(Long.MAX_VALUE)) <= 0;
  }

  private long buildBigIntegerTerm(BigInteger value) throws Exception {
    BigInteger abs = value.abs();
    long term = buildBigIntFromNonNegative(abs);
    if (value.signum() < 0) {
      term =
          makeUnary(
              "-",
              FunctionDeclarationKind.UMINUS,
              FormulaType.IntegerType,
              term,
              LeanSmtNativeApi::mkNeg);
    }
    return term;
  }

  private long buildBigIntFromNonNegative(BigInteger value) throws Exception {
    Preconditions.checkArgument(value.signum() >= 0, "Expected non-negative value");
    if (fitsInLong(value)) {
      return makeRegisteredIntLiteral(value.longValue());
    }

    // Encode very large integers in base 10^9 chunks to avoid lossy 64-bit conversions in native
    // constructors while still building a pure arithmetic term.
    List<Long> chunks = new ArrayList<>();
    BigInteger remaining = value;
    while (remaining.signum() > 0) {
      BigInteger[] qr = remaining.divideAndRemainder(INT_CHUNK_BASE);
      chunks.add(makeRegisteredIntLiteral(qr[1].longValue()));
      remaining = qr[0];
    }

    long baseHandle = makeRegisteredIntLiteral(INT_CHUNK_BASE.longValue());
    long result = chunks.get(chunks.size() - 1);
    for (int i = chunks.size() - 2; i >= 0; i--) {
      long mul =
          makeBinary(
              "*",
              FunctionDeclarationKind.MUL,
              FormulaType.IntegerType,
              result,
              baseHandle,
              LeanSmtNativeApi::mkMul);
      result =
          makeBinary(
              "+",
              FunctionDeclarationKind.ADD,
              FormulaType.IntegerType,
              mul,
              chunks.get(i),
              LeanSmtNativeApi::mkAdd);
    }
    return result;
  }

  private long buildBigRealFromNonNegativeInteger(BigInteger value) throws Exception {
    Preconditions.checkArgument(value.signum() >= 0, "Expected non-negative value");
    if (fitsInLong(value)) {
      return makeRegisteredRealLiteral(value.longValue());
    }

    // Same chunking strategy as integers, but emitted as exact real literals n/1.
    List<Long> chunks = new ArrayList<>();
    BigInteger remaining = value;
    while (remaining.signum() > 0) {
      BigInteger[] qr = remaining.divideAndRemainder(INT_CHUNK_BASE);
      chunks.add(makeRegisteredRealLiteral(qr[1].longValue()));
      remaining = qr[0];
    }

    long baseHandle = makeRegisteredRealLiteral(INT_CHUNK_BASE.longValue());
    long result = chunks.get(chunks.size() - 1);
    for (int i = chunks.size() - 2; i >= 0; i--) {
      long mul =
          makeBinary(
              "*",
              FunctionDeclarationKind.MUL,
              FormulaType.RationalType,
              result,
              baseHandle,
              LeanSmtNativeApi::mkMul);
      result =
          makeBinary(
              "+",
              FunctionDeclarationKind.ADD,
              FormulaType.RationalType,
              mul,
              chunks.get(i),
              LeanSmtNativeApi::mkAdd);
    }
    return result;
  }

  private void registerApplication(long handle, FunctionDeclarationKind kind, FormulaType<?> type) {
    formulaTypes.put(handle, type);
    declarationKinds.put(handle, kind);
  }

  private long makeRegisteredIntLiteral(long value) throws Exception {
    long handle = LeanSmtNativeApi.mkIntConst(value);
    registerConstant(handle, FormulaType.IntegerType, BigInteger.valueOf(value));
    return handle;
  }

  private long makeRegisteredRealLiteral(long value) throws Exception {
    long handle = LeanSmtNativeApi.mkRealConst(value, 1L);
    registerConstant(handle, FormulaType.RationalType, Rational.ofLongs(value, 1L));
    return handle;
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
    return makeUnary(
        "to_int",
        FunctionDeclarationKind.FLOOR,
        FormulaType.IntegerType,
        argument,
        arg -> LeanSmtNativeApi.mkApp1("to_int", arg));
  }

  long makeIntToBitvectorTerm(int bitwidth, long integerTerm) {
    Preconditions.checkArgument(bitwidth > 0, "Bitvector size must be positive");
    return makeUnary(
        intToBvSymbol(bitwidth),
        FunctionDeclarationKind.INT_TO_BV,
        FormulaType.getBitvectorTypeWithSize(bitwidth),
        integerTerm,
        arg -> LeanSmtNativeApi.mkIndexedApp1("int_to_bv", bitwidth, arg));
  }

  private static String intToBvSymbol(int bitwidth) {
    return "(_ int_to_bv " + bitwidth + ")";
  }

  private long buildExactRationalTerm(Rational value) throws Exception {
    BigInteger num = value.getNum();
    BigInteger den = value.getDen();

    long numTerm = buildBigRealFromNonNegativeInteger(num.abs());
    if (num.signum() < 0) {
      numTerm =
          makeUnary(
              "-",
              FunctionDeclarationKind.UMINUS,
              FormulaType.RationalType,
              numTerm,
              LeanSmtNativeApi::mkNeg);
    }
    long denTerm = buildBigRealFromNonNegativeInteger(den);
    return makeBinary(
        "/",
        FunctionDeclarationKind.DIV,
        FormulaType.RationalType,
        numTerm,
        denTerm,
        (left, right) -> LeanSmtNativeApi.mkApp2("/", left, right));
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

    @Nullable Long handled = tryHandleCoreBuiltInFunction(declaration, args, kind, returnType, symbol);
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
        return makeUnary("not", kind, FormulaType.BooleanType, args.get(0), LeanSmtNativeApi::mkNot);
      case AND:
        return foldAnd(args);
      case OR:
        return foldOr(args);
      case XOR:
        return foldLeft("xor", kind, FormulaType.BooleanType, args, LeanSmtNativeApi::mkXor);
      case IMPLIES:
        return foldLeft("=>", kind, FormulaType.BooleanType, args, LeanSmtNativeApi::mkImplies);
      case ITE:
        checkArity(declaration, args, 3);
        return makeTernary(
            "ite",
            kind,
            returnType,
            args.get(0),
            args.get(1),
            args.get(2),
            LeanSmtNativeApi::mkIte);
      case EQ:
        return foldPairwiseBoolean("=", kind, args, LeanSmtNativeApi::mkEq);
      case DISTINCT:
        return foldAllDistinct(args);
      case LT:
        return foldPairwiseBoolean("<", kind, args, LeanSmtNativeApi::mkLt);
      case LTE:
        return foldPairwiseBoolean("<=", kind, args, LeanSmtNativeApi::mkLe);
      case GT:
        return foldPairwiseBoolean(">", kind, args, LeanSmtNativeApi::mkGt);
      case GTE:
        return foldPairwiseBoolean(">=", kind, args, LeanSmtNativeApi::mkGe);
      case ADD:
        return foldLeft("+", kind, returnType, args, LeanSmtNativeApi::mkAdd);
      case SUB:
        if (args.size() == 1) {
          return makeUnary(
              "-", FunctionDeclarationKind.UMINUS, returnType, args.get(0), LeanSmtNativeApi::mkNeg);
        }
        return foldLeft("-", kind, returnType, args, LeanSmtNativeApi::mkSub);
      case MUL:
        return foldLeft("*", kind, returnType, args, LeanSmtNativeApi::mkMul);
      case DIV:
        if (returnType.isRationalType()) {
          return foldLeft(
              "/",
              kind,
              returnType,
              args,
              (left, right) -> LeanSmtNativeApi.mkApp2("/", left, right));
        }
        return foldLeft("div", kind, returnType, args, LeanSmtNativeApi::mkDiv);
      case MODULO:
        return foldLeft("mod", kind, returnType, args, LeanSmtNativeApi::mkMod);
      case UMINUS:
        checkArity(declaration, args, 1);
        return makeUnary("-", kind, returnType, args.get(0), LeanSmtNativeApi::mkNeg);
      case TO_REAL:
        checkArity(declaration, args, 1);
        return makeUnary(
            "to_real",
            kind,
            FormulaType.RationalType,
            args.get(0),
            arg -> LeanSmtNativeApi.mkApp1("to_real", arg));
      case FLOOR:
        checkArity(declaration, args, 1);
        return makeFloorTerm(args.get(0));
      case INT_TO_BV:
        checkArity(declaration, args, 1);
        return makeIntToBitvectorTerm(parseIntToBvWidth(declaration, returnType), args.get(0));
      case BV_EXTRACT:
        checkArity(declaration, args, 1);
        int[] extract = parseExtractIndices(symbol);
        return makeUnary(
            symbol,
            kind,
            returnType,
            args.get(0),
            arg -> LeanSmtNativeApi.mkExtract(arg, extract[0], extract[1]));
      case BV_SIGN_EXTENSION:
      case BV_ZERO_EXTENSION:
        checkArity(declaration, args, 1);
        String extendOp =
            kind == FunctionDeclarationKind.BV_SIGN_EXTENSION ? "sign_extend" : "zero_extend";
        int extensionBits = parseIndexedUnaryParameter(symbol, extendOp);
        return makeUnary(
            symbol,
            kind,
            returnType,
            args.get(0),
            arg -> LeanSmtNativeApi.mkIndexedApp1(extendOp, extensionBits, arg));
      case BV_ROTATE_LEFT_BY_INT:
      case BV_ROTATE_RIGHT_BY_INT:
        checkArity(declaration, args, 1);
        String rotateByIntOp =
            kind == FunctionDeclarationKind.BV_ROTATE_LEFT_BY_INT ? "rotate_left" : "rotate_right";
        int rotateAmount = parseIndexedUnaryParameter(symbol, rotateByIntOp);
        return makeUnary(
            symbol,
            kind,
            returnType,
            args.get(0),
            arg -> LeanSmtNativeApi.mkIndexedApp1(rotateByIntOp, rotateAmount, arg));
      case BV_NOT:
      case BV_NEG:
      case UBV_TO_INT:
        checkArity(declaration, args, 1);
        return makeUnary(
            symbol, kind, returnType, args.get(0), arg -> LeanSmtNativeApi.mkApp1(symbol, arg));
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
        checkArity(declaration, args, 2);
        return makeBinary(
            symbol,
            kind,
            returnType,
            args.get(0),
            args.get(1),
            (left, right) -> LeanSmtNativeApi.mkApp2(symbol, left, right));
      case BV_ROTATE_LEFT:
        checkArity(declaration, args, 2);
        return rebuildSymbolicRotateLeft(args);
      case BV_ROTATE_RIGHT:
        checkArity(declaration, args, 2);
        return rebuildSymbolicRotateRight(args);
      case BV_EQ:
        return foldPairwiseBoolean("=", kind, args, LeanSmtNativeApi::mkEq);
      case BV_ULT:
      case BV_ULE:
      case BV_UGT:
      case BV_UGE:
      case BV_SLT:
      case BV_SLE:
      case BV_SGT:
      case BV_SGE:
        checkArity(declaration, args, 2);
        return makeBinary(
            symbol,
            kind,
            FormulaType.BooleanType,
            args.get(0),
            args.get(1),
            (left, right) -> LeanSmtNativeApi.mkApp2(symbol, left, right));
      default:
        return null;
    }
  }

  private int bitvectorSize(long term) {
    FormulaType<?> type = getFormulaType(term);
    Preconditions.checkArgument(type.isBitvectorType(), "Expected bitvector term, got %s", type);
    return ((FormulaType.BitvectorType) type).getSize();
  }

  // Shared lowering for symbolic signed bitvector-to-integer conversion.
  long makeSignedBitvectorToIntegerTerm(long bitvectorTerm) {
    return makeUnary(
        "sbv_to_int",
        FunctionDeclarationKind.SBV_TO_INT,
        FormulaType.IntegerType,
        bitvectorTerm,
        arg -> LeanSmtNativeApi.mkApp1("sbv_to_int", arg));
  }

  private Long rebuildSymbolicRotateLeft(List<Long> args) {
    int width = bitvectorSize(args.get(0));
    FormulaType<?> bitvectorType = FormulaType.getBitvectorTypeWithSize(width);
    Preconditions.checkArgument(
        bitvectorSize(args.get(1)) == width,
        "Can't rotate bitvectors with different sizes (%s and %s)",
        width,
        bitvectorSize(args.get(1)));

    long widthTerm = makeBitvectorConstant(width, BigInteger.valueOf(width));
    long rotateAmount =
        makeBinary(
            "bvurem",
            FunctionDeclarationKind.BV_UREM,
            bitvectorType,
            args.get(1),
            widthTerm,
            (left, right) -> LeanSmtNativeApi.mkApp2("bvurem", left, right));
    long shiftLeft =
        makeBinary(
            "bvshl",
            FunctionDeclarationKind.BV_SHL,
            bitvectorType,
            args.get(0),
            rotateAmount,
            (left, right) -> LeanSmtNativeApi.mkApp2("bvshl", left, right));
    long remainingWidth =
        makeBinary(
            "bvsub",
            FunctionDeclarationKind.BV_SUB,
            bitvectorType,
            widthTerm,
            rotateAmount,
            (left, right) -> LeanSmtNativeApi.mkApp2("bvsub", left, right));
    long shiftRight =
        makeBinary(
            "bvlshr",
            FunctionDeclarationKind.BV_LSHR,
            bitvectorType,
            args.get(0),
            remainingWidth,
            (left, right) -> LeanSmtNativeApi.mkApp2("bvlshr", left, right));
    return makeBinary(
        "bvor",
        FunctionDeclarationKind.BV_OR,
        bitvectorType,
        shiftLeft,
        shiftRight,
        (left, right) -> LeanSmtNativeApi.mkApp2("bvor", left, right));
  }

  private Long rebuildSymbolicRotateRight(List<Long> args) {
    int width = bitvectorSize(args.get(0));
    FormulaType<?> bitvectorType = FormulaType.getBitvectorTypeWithSize(width);
    Preconditions.checkArgument(
        bitvectorSize(args.get(1)) == width,
        "Can't rotate bitvectors with different sizes (%s and %s)",
        width,
        bitvectorSize(args.get(1)));

    long widthTerm = makeBitvectorConstant(width, BigInteger.valueOf(width));
    long rotateAmount =
        makeBinary(
            "bvurem",
            FunctionDeclarationKind.BV_UREM,
            bitvectorType,
            args.get(1),
            widthTerm,
            (left, right) -> LeanSmtNativeApi.mkApp2("bvurem", left, right));
    long shiftRight =
        makeBinary(
            "bvlshr",
            FunctionDeclarationKind.BV_LSHR,
            bitvectorType,
            args.get(0),
            rotateAmount,
            (left, right) -> LeanSmtNativeApi.mkApp2("bvlshr", left, right));
    long remainingWidth =
        makeBinary(
            "bvsub",
            FunctionDeclarationKind.BV_SUB,
            bitvectorType,
            widthTerm,
            rotateAmount,
            (left, right) -> LeanSmtNativeApi.mkApp2("bvsub", left, right));
    long shiftLeft =
        makeBinary(
            "bvshl",
            FunctionDeclarationKind.BV_SHL,
            bitvectorType,
            args.get(0),
            remainingWidth,
            (left, right) -> LeanSmtNativeApi.mkApp2("bvshl", left, right));
    return makeBinary(
        "bvor",
        FunctionDeclarationKind.BV_OR,
        bitvectorType,
        shiftRight,
        shiftLeft,
        (left, right) -> LeanSmtNativeApi.mkApp2("bvor", left, right));
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
      throw new IllegalArgumentException(
          "Expected extract with msb >= lsb, got '" + symbol + "'");
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
              "and",
              FunctionDeclarationKind.AND,
              FormulaType.BooleanType,
              result,
              args.get(i),
              LeanSmtNativeApi::mkAnd);
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
              "or",
              FunctionDeclarationKind.OR,
              FormulaType.BooleanType,
              result,
              args.get(i),
              LeanSmtNativeApi::mkOr);
    }
    return result;
  }

  private long foldLeft(
      String symbol,
      FunctionDeclarationKind kind,
      FormulaType<?> type,
      List<Long> args,
      NativeBinary nativeOp) {
    if (args.isEmpty()) {
      throw new IllegalArgumentException("Cannot apply " + kind + " to empty argument list");
    }
    long result = args.get(0);
    for (int i = 1; i < args.size(); i++) {
      result = makeBinary(symbol, kind, type, result, args.get(i), nativeOp);
    }
    return result;
  }

  private long foldPairwiseBoolean(
      String symbol, FunctionDeclarationKind kind, List<Long> args, NativeBinary nativeOp) {
    if (args.size() < 2) {
      return getTrueHandle();
    }
    long result =
        makeBinary(symbol, kind, FormulaType.BooleanType, args.get(0), args.get(1), nativeOp);
    for (int i = 2; i < args.size(); i++) {
      long next =
          makeBinary(symbol, kind, FormulaType.BooleanType, args.get(i - 1), args.get(i), nativeOp);
      result =
          makeBinary(
              "and",
              FunctionDeclarationKind.AND,
              FormulaType.BooleanType,
              result,
              next,
              LeanSmtNativeApi::mkAnd);
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
                args.get(j),
                LeanSmtNativeApi::mkDistinct);
        if (result == null) {
          result = neq;
        } else {
          result =
              makeBinary(
                  "and",
                  FunctionDeclarationKind.AND,
                  FormulaType.BooleanType,
                  result,
                  neq,
                  LeanSmtNativeApi::mkAnd);
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

  @FunctionalInterface
  interface NativeUnary {
    long apply(long a) throws Exception;
  }

  @FunctionalInterface
  interface NativeBinary {
    long apply(long a, long b) throws Exception;
  }

  @FunctionalInterface
  interface NativeTernary {
    long apply(long a, long b, long c) throws Exception;
  }
}
