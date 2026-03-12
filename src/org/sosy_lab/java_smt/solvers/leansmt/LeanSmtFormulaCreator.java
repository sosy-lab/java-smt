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
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;
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

  private final Map<Long, Expr> expressions = new ConcurrentHashMap<>();
  private final Map<String, LeanSmtType> declaredVariables = new LinkedHashMap<>();
  private final Map<String, Long> latestVariableHandles = new LinkedHashMap<>();
  private final Map<Long, LeanSmtFunctionDecl> booleanVarDeclarations = new ConcurrentHashMap<>();
  private final Map<BigInteger, Long> intConstantHandles = new HashMap<>();
  private final Map<Rational, Long> realConstantHandles = new HashMap<>();
  private final Map<BitvectorConstantKey, Long> bitvectorConstantHandles = new HashMap<>();
  private final Map<OperationKey, Long> canonicalApplications = new HashMap<>();
  private final Map<ApplicationKey, Long> ufApplications = new HashMap<>();
  private final Map<LeanSmtFunctionDecl, List<UfApplication>> ufApplicationsByDecl = new HashMap<>();
  private final AtomicLong ufFreshCounter = new AtomicLong(0);
  private final AtomicLong floorFreshCounter = new AtomicLong(0);
  private final AtomicLong intToBvFreshCounter = new AtomicLong(0);
  private final AtomicLong rationalConstFreshCounter = new AtomicLong(0);
  private final List<Long> ufCongruenceConstraints = new ArrayList<>();
  private final Map<Long, Long> floorTermsByArgument = new HashMap<>();
  private final List<Long> floorConstraints = new ArrayList<>();
  private final Map<IntToBvKey, Long> intToBvTerms = new HashMap<>();
  private final List<Long> intToBvConstraints = new ArrayList<>();
  private final Map<Rational, Long> constrainedRationalConstants = new HashMap<>();
  private final List<Long> rationalConstantConstraints = new ArrayList<>();
  private boolean ufCongruenceDirty = false;
  private final long trueHandle;
  private final long falseHandle;

  LeanSmtFormulaCreator(long pConstructionSolver) {
    super(pConstructionSolver, LeanSmtType.BOOL, LeanSmtType.INT, LeanSmtType.REAL, null, null);
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
        final long handle;
        if (type.isBool()) {
          handle = LeanSmtNativeApi.mkBoolVar(getEnv(), varName);
        } else if (type.isInt()) {
          handle = LeanSmtNativeApi.mkIntVar(getEnv(), varName);
        } else if (type.isReal()) {
          handle = LeanSmtNativeApi.mkRealVar(getEnv(), varName);
        } else if (type.isBitvector()) {
          handle = LeanSmtNativeApi.mkBvVar(getEnv(), varName, type.getBitvectorSize());
        } else {
          throw new AssertionError("Unexpected LeanSMT type " + type);
        }
        registerVariable(handle, varName, type);
        return handle;
      } catch (Exception e) {
        throw new IllegalArgumentException("Failed to create variable in LeanSMT: " + varName, e);
      }
    }
  }

  synchronized void redeclareAllVariables(long solver) {
    for (Map.Entry<String, LeanSmtType> entry : declaredVariables.entrySet()) {
      declareVariableOnSolver(solver, entry.getKey(), entry.getValue());
    }
  }

  synchronized void redeclareMissingVariables(long solver, Set<String> alreadyDeclared) {
    for (Map.Entry<String, LeanSmtType> entry : declaredVariables.entrySet()) {
      if (alreadyDeclared.contains(entry.getKey())) {
        continue;
      }
      declareVariableOnSolver(solver, entry.getKey(), entry.getValue());
      alreadyDeclared.add(entry.getKey());
    }
  }

  synchronized ImmutableMap<String, Long> getKnownVariableHandles() {
    return ImmutableMap.copyOf(latestVariableHandles);
  }

  synchronized ImmutableMap<String, Long> getKnownUserVariableHandles() {
    ImmutableMap.Builder<String, Long> out = ImmutableMap.builder();
    for (Map.Entry<String, Long> entry : latestVariableHandles.entrySet()) {
      String name = entry.getKey();
      if (name.startsWith("__floor#")
          || name.startsWith("__int2bv#")
          || name.startsWith("__ratc#")) {
        continue;
      }
      out.put(name, entry.getValue());
    }
    return out.build();
  }

  synchronized ImmutableMap<String, LeanSmtType> getDeclaredVariableTypes() {
    return ImmutableMap.copyOf(declaredVariables);
  }

  List<LeanSmtFunctionDecl> getKnownUfDeclarations() {
    synchronized (ufApplications) {
      return ImmutableList.copyOf(ufApplicationsByDecl.keySet());
    }
  }

  long getConstructionSolver() {
    return getEnv();
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
        if (fitsInLong(value)) {
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
        if (fitsInLong(num) && fitsInLong(den)) {
          handle = LeanSmtNativeApi.mkRealConst(num.longValue(), den.longValue());
        } else if (den.equals(BigInteger.ONE)) {
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
          handle = makeConstrainedRationalConstant(value);
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
        registerApplication(handle, symbol, kind, type, arguments);
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
        registerApplication(handle, symbol, kind, type, arguments);
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
        registerApplication(handle, symbol, kind, type, arguments);
        canonicalApplications.put(key, handle);
        return handle;
      } catch (Exception e) {
        throw new IllegalArgumentException("Failed to create term '" + symbol + "'", e);
      }
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
    if (expr == null) {
      return null;
    }
    if (expr.kind == ExprKind.CONSTANT) {
      Object value = expr.constantValue;
      if (value instanceof Boolean || value instanceof BigInteger || value instanceof Rational) {
        return value;
      }
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
        return visitor.visitConstant(formula, expr.constantValue);

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

    synchronized (ufApplications) {
      ApplicationKey key = new ApplicationKey(declaration, ImmutableList.copyOf(args));
      Long existing = ufApplications.get(key);
      if (existing != null) {
        return existing;
      }

      long handle = createUfApplicationHandle(declaration);
      registerApplication(
          handle,
          declaration.getName(),
          FunctionDeclarationKind.UF,
          declaration.getReturnType().toFormulaType(),
          key.args);
      ufApplications.put(key, handle);
      ufApplicationsByDecl
          .computeIfAbsent(declaration, ignored -> new ArrayList<>())
          .add(new UfApplication(handle, key.args));
      ufCongruenceDirty = true;
      return handle;
    }
  }

  @Override
  public LeanSmtFunctionDecl declareUFImpl(
      String name, LeanSmtType returnType, List<LeanSmtType> argTypes) {
    return new LeanSmtFunctionDecl(
        name, FunctionDeclarationKind.UF, returnType, ImmutableList.copyOf(argTypes));
  }

  @Override
  protected LeanSmtFunctionDecl getBooleanVarDeclarationImpl(Long formulaInfo) {
    LeanSmtFunctionDecl declaration = booleanVarDeclarations.get(formulaInfo);
    if (declaration == null) {
      throw new UnsupportedOperationException(
          "LeanSMT term is not a declared Boolean variable: " + formulaInfo);
    }
    return declaration;
  }

  private synchronized void registerVariable(long handle, String name, LeanSmtType type) {
    declaredVariables.put(name, type);
    latestVariableHandles.put(name, handle);
    FormulaType<?> formulaType = type.toFormulaType();
    expressions.put(
        handle,
        new Expr(
            ExprKind.VARIABLE,
            formulaType,
            name,
            null,
            FunctionDeclarationKind.VAR,
            ImmutableList.of()));
    if (type.isBool()) {
      booleanVarDeclarations.put(
          handle,
          new LeanSmtFunctionDecl(
              name, FunctionDeclarationKind.VAR, LeanSmtType.BOOL, ImmutableList.of()));
    }
  }

  private void declareVariableOnSolver(long solver, String name, LeanSmtType type) {
    try {
      if (type.isBool()) {
        LeanSmtNativeApi.mkBoolVar(solver, name);
      } else if (type.isInt()) {
        LeanSmtNativeApi.mkIntVar(solver, name);
      } else if (type.isReal()) {
        LeanSmtNativeApi.mkRealVar(solver, name);
      } else if (type.isBitvector()) {
        LeanSmtNativeApi.mkBvVar(solver, name, type.getBitvectorSize());
      } else {
        throw new AssertionError("Unexpected LeanSMT type " + type);
      }
    } catch (Exception e) {
      throw new IllegalStateException("Failed to declare variable " + name, e);
    }
  }

  private void registerConstant(long handle, FormulaType<?> type, Object value) {
    expressions.put(
        handle,
        new Expr(
            ExprKind.CONSTANT, type, value.toString(), value, FunctionDeclarationKind.CONST, ImmutableList.of()));
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
      return LeanSmtNativeApi.mkIntConst(value.longValue());
    }

    // Encode very large integers in base 10^9 chunks to avoid lossy 64-bit conversions in native
    // constructors while still building a pure arithmetic term.
    List<Long> chunks = new ArrayList<>();
    BigInteger remaining = value;
    while (remaining.signum() > 0) {
      BigInteger[] qr = remaining.divideAndRemainder(INT_CHUNK_BASE);
      chunks.add(LeanSmtNativeApi.mkIntConst(qr[1].longValue()));
      remaining = qr[0];
    }

    long baseHandle = LeanSmtNativeApi.mkIntConst(INT_CHUNK_BASE.longValue());
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
      return LeanSmtNativeApi.mkRealConst(value.longValue(), 1L);
    }

    // Same chunking strategy as integers, but emitted as exact real literals n/1.
    List<Long> chunks = new ArrayList<>();
    BigInteger remaining = value;
    while (remaining.signum() > 0) {
      BigInteger[] qr = remaining.divideAndRemainder(INT_CHUNK_BASE);
      chunks.add(LeanSmtNativeApi.mkRealConst(qr[1].longValue(), 1L));
      remaining = qr[0];
    }

    long baseHandle = LeanSmtNativeApi.mkRealConst(INT_CHUNK_BASE.longValue(), 1L);
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

  private void registerApplication(
      long handle,
      String symbol,
      FunctionDeclarationKind kind,
      FormulaType<?> type,
      ImmutableList<Long> arguments) {
    expressions.put(handle, new Expr(ExprKind.APPLICATION, type, symbol, null, kind, arguments));
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

  List<Long> getUfCongruenceConstraints() {
    synchronized (ufApplications) {
      if (!ufCongruenceDirty) {
        return ImmutableList.copyOf(ufCongruenceConstraints);
      }
      // Recompute only when the UF application set changed. This keeps check-sat overhead stable
      // across repeated calls with unchanged formulas.
      ufCongruenceConstraints.clear();
      for (Map.Entry<LeanSmtFunctionDecl, List<UfApplication>> entry : ufApplicationsByDecl.entrySet()) {
        List<UfApplication> apps = entry.getValue();
        for (int i = 0; i < apps.size(); i++) {
          for (int j = i + 1; j < apps.size(); j++) {
            ufCongruenceConstraints.add(buildCongruenceConstraint(apps.get(i), apps.get(j)));
          }
        }
      }
      ufCongruenceDirty = false;
      return ImmutableList.copyOf(ufCongruenceConstraints);
    }
  }

  List<Long> getFloorConstraints() {
    synchronized (floorTermsByArgument) {
      return ImmutableList.copyOf(floorConstraints);
    }
  }

  List<Long> getRationalConstantConstraints() {
    synchronized (constrainedRationalConstants) {
      return ImmutableList.copyOf(rationalConstantConstraints);
    }
  }

  List<Long> getIntToBvConstraints() {
    synchronized (intToBvTerms) {
      return ImmutableList.copyOf(intToBvConstraints);
    }
  }

  long makeFloorTerm(long argument) {
    synchronized (floorTermsByArgument) {
      Long existing = floorTermsByArgument.get(argument);
      if (existing != null) {
        return existing;
      }
      String freshName = "__floor#" + floorFreshCounter.incrementAndGet();
      long floorHandle = makeVariable(LeanSmtType.INT, freshName);

      // Preserve semantic structure for visitors, while the native term is represented by an
      // internal Int variable constrained to be floor(argument).
      registerApplication(
          floorHandle,
          "floor",
          FunctionDeclarationKind.FLOOR,
          FormulaType.IntegerType,
          ImmutableList.of(argument));

      long one = makeIntConstant(1L);
      long floorLeArg =
          makeBinary(
              "<=",
              FunctionDeclarationKind.LTE,
              FormulaType.BooleanType,
              floorHandle,
              argument,
              LeanSmtNativeApi::mkLe);
      long floorPlusOne =
          makeBinary(
              "+",
              FunctionDeclarationKind.ADD,
              FormulaType.IntegerType,
              floorHandle,
              one,
              LeanSmtNativeApi::mkAdd);
      long argLtFloorPlusOne =
          makeBinary(
              "<",
              FunctionDeclarationKind.LT,
              FormulaType.BooleanType,
              argument,
              floorPlusOne,
              LeanSmtNativeApi::mkLt);

      floorConstraints.add(floorLeArg);
      floorConstraints.add(argLtFloorPlusOne);
      floorTermsByArgument.put(argument, floorHandle);
      return floorHandle;
    }
  }

  long makeIntToBitvectorTerm(int bitwidth, long integerTerm) {
    Preconditions.checkArgument(bitwidth > 0, "Bitvector size must be positive");
    Object value = convertValue(integerTerm);
    if (value instanceof BigInteger) {
      BigInteger modulus = BigInteger.ONE.shiftLeft(bitwidth);
      BigInteger normalized = ((BigInteger) value).mod(modulus);
      return makeBitvectorConstant(bitwidth, normalized);
    }
    synchronized (intToBvTerms) {
      IntToBvKey key = new IntToBvKey(bitwidth, integerTerm);
      Long existing = intToBvTerms.get(key);
      if (existing != null) {
        return existing;
      }

      String freshName = "__int2bv#" + intToBvFreshCounter.incrementAndGet();
      long bvHandle = makeVariable(LeanSmtType.bitvector(bitwidth), freshName);
      registerApplication(
          bvHandle,
          intToBvSymbol(bitwidth),
          FunctionDeclarationKind.INT_TO_BV,
          FormulaType.getBitvectorTypeWithSize(bitwidth),
          ImmutableList.of(integerTerm));

      long asInt =
          makeUnary(
              "ubv_to_int",
              FunctionDeclarationKind.UBV_TO_INT,
              FormulaType.IntegerType,
              bvHandle,
              arg -> LeanSmtNativeApi.mkApp1("ubv_to_int", arg));

      long modulus = makeIntConstant(BigInteger.ONE.shiftLeft(bitwidth));
      long normalized =
          makeBinary(
              "mod",
              FunctionDeclarationKind.MODULO,
              FormulaType.IntegerType,
              integerTerm,
              modulus,
              LeanSmtNativeApi::mkMod);
      long constraint =
          makeBinary(
              "=",
              FunctionDeclarationKind.EQ,
              FormulaType.BooleanType,
              asInt,
              normalized,
              LeanSmtNativeApi::mkEq);

      intToBvConstraints.add(constraint);
      intToBvTerms.put(key, bvHandle);
      return bvHandle;
    }
  }

  private static String intToBvSymbol(int bitwidth) {
    return "(_ int_to_bv " + bitwidth + ")";
  }

  private long createUfApplicationHandle(LeanSmtFunctionDecl declaration) {
    String freshName = declaration.getName() + "@uf#" + ufFreshCounter.incrementAndGet();
    return makeVariable(declaration.getReturnType(), freshName);
  }

  private long buildCongruenceConstraint(UfApplication a, UfApplication b) {
    Preconditions.checkArgument(
        a.arguments.size() == b.arguments.size(), "UF arity mismatch in congruence construction");
    long lhs;
    if (a.arguments.isEmpty()) {
      lhs = getTrueHandle();
    } else {
      lhs =
          makeBinary(
              "=",
              FunctionDeclarationKind.EQ,
              FormulaType.BooleanType,
              a.arguments.get(0),
              b.arguments.get(0),
              LeanSmtNativeApi::mkEq);
      for (int i = 1; i < a.arguments.size(); i++) {
        long eqArg =
            makeBinary(
                "=",
                FunctionDeclarationKind.EQ,
                FormulaType.BooleanType,
                a.arguments.get(i),
                b.arguments.get(i),
                LeanSmtNativeApi::mkEq);
        lhs =
            makeBinary(
                "and",
                FunctionDeclarationKind.AND,
                FormulaType.BooleanType,
                lhs,
                eqArg,
                LeanSmtNativeApi::mkAnd);
      }
    }

    long rhs =
        makeBinary(
            "=",
            FunctionDeclarationKind.EQ,
            FormulaType.BooleanType,
            a.handle,
            b.handle,
            LeanSmtNativeApi::mkEq);

    return makeBinary(
        "=>",
        FunctionDeclarationKind.IMPLIES,
        FormulaType.BooleanType,
        lhs,
        rhs,
        LeanSmtNativeApi::mkImplies);
  }

  private long makeConstrainedRationalConstant(Rational value) throws Exception {
    synchronized (constrainedRationalConstants) {
      Long existing = constrainedRationalConstants.get(value);
      if (existing != null) {
        return existing;
      }

      String freshName = "__ratc#" + rationalConstFreshCounter.incrementAndGet();
      long handle = makeVariable(LeanSmtType.REAL, freshName);
      BigInteger num = value.getNum();
      BigInteger den = value.getDen();

      // For large rationals, avoid relying on native division constructor behavior. Instead encode
      // the exact value via den * c = num and treat c as the constant term.
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
      long lhs =
          makeBinary(
              "*",
              FunctionDeclarationKind.MUL,
              FormulaType.RationalType,
              denTerm,
              handle,
              LeanSmtNativeApi::mkMul);
      long eq =
          makeBinary(
              "=",
              FunctionDeclarationKind.EQ,
              FormulaType.BooleanType,
              lhs,
              numTerm,
              LeanSmtNativeApi::mkEq);
      rationalConstantConstraints.add(eq);
      constrainedRationalConstants.put(value, handle);
      return handle;
    }
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
        return makeBinary(
            symbol,
            kind,
            returnType,
            args.get(0),
            args.get(1),
            this::buildRotateLeftTerm);
      case BV_ROTATE_RIGHT:
        checkArity(declaration, args, 2);
        return makeBinary(
            symbol,
            kind,
            returnType,
            args.get(0),
            args.get(1),
            this::buildRotateRightTerm);
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
    int size = bitvectorSize(bitvectorTerm);
    BigInteger modulus = BigInteger.ONE.shiftLeft(size);

    return makeUnary(
        "sbv_to_int",
        FunctionDeclarationKind.SBV_TO_INT,
        FormulaType.IntegerType,
        bitvectorTerm,
        arg -> {
          long unsignedArg =
              makeUnary(
                  "ubv_to_int",
                  FunctionDeclarationKind.UBV_TO_INT,
                  FormulaType.IntegerType,
                  arg,
                  t -> LeanSmtNativeApi.mkApp1("ubv_to_int", t));
          long zero = makeBitvectorConstant(size, BigInteger.ZERO);
          long isNegative =
              makeBinary(
                  "bvslt",
                  FunctionDeclarationKind.BV_SLT,
                  FormulaType.BooleanType,
                  arg,
                  zero,
                  (a, b) -> LeanSmtNativeApi.mkApp2("bvslt", a, b));
          long modulusInt = makeIntConstant(modulus);
          long adjusted =
              makeBinary(
                  "-",
                  FunctionDeclarationKind.SUB,
                  FormulaType.IntegerType,
                  unsignedArg,
                  modulusInt,
                  LeanSmtNativeApi::mkSub);
          return makeTernary(
              "ite",
              FunctionDeclarationKind.ITE,
              FormulaType.IntegerType,
              isNegative,
              adjusted,
              unsignedArg,
              LeanSmtNativeApi::mkIte);
        });
  }

  long buildRotateLeftTerm(long bitvector, long rotationAmount) throws Exception {
    int size = bitvectorSize(bitvector);
    long sizeBv = makeBitvectorConstant(size, BigInteger.valueOf(size));
    long rotateInRange =
        makeBinary(
            "bvurem",
            FunctionDeclarationKind.BV_UREM,
            getFormulaType(bitvector),
            rotationAmount,
            sizeBv,
            (a, b) -> LeanSmtNativeApi.mkApp2("bvurem", a, b));
    long left =
        makeBinary(
            "bvshl",
            FunctionDeclarationKind.BV_SHL,
            getFormulaType(bitvector),
            bitvector,
            rotateInRange,
            (a, b) -> LeanSmtNativeApi.mkApp2("bvshl", a, b));
    long remaining =
        makeBinary(
            "bvsub",
            FunctionDeclarationKind.BV_SUB,
            getFormulaType(bitvector),
            sizeBv,
            rotateInRange,
            (a, b) -> LeanSmtNativeApi.mkApp2("bvsub", a, b));
    long right =
        makeBinary(
            "bvlshr",
            FunctionDeclarationKind.BV_LSHR,
            getFormulaType(bitvector),
            bitvector,
            remaining,
            (a, b) -> LeanSmtNativeApi.mkApp2("bvlshr", a, b));
    return makeBinary(
        "bvor",
        FunctionDeclarationKind.BV_OR,
        getFormulaType(bitvector),
        left,
        right,
        (a, b) -> LeanSmtNativeApi.mkApp2("bvor", a, b));
  }

  long buildRotateRightTerm(long bitvector, long rotationAmount) throws Exception {
    int size = bitvectorSize(bitvector);
    long sizeBv = makeBitvectorConstant(size, BigInteger.valueOf(size));
    long rotateInRange =
        makeBinary(
            "bvurem",
            FunctionDeclarationKind.BV_UREM,
            getFormulaType(bitvector),
            rotationAmount,
            sizeBv,
            (a, b) -> LeanSmtNativeApi.mkApp2("bvurem", a, b));
    long right =
        makeBinary(
            "bvlshr",
            FunctionDeclarationKind.BV_LSHR,
            getFormulaType(bitvector),
            bitvector,
            rotateInRange,
            (a, b) -> LeanSmtNativeApi.mkApp2("bvlshr", a, b));
    long remaining =
        makeBinary(
            "bvsub",
            FunctionDeclarationKind.BV_SUB,
            getFormulaType(bitvector),
            sizeBv,
            rotateInRange,
            (a, b) -> LeanSmtNativeApi.mkApp2("bvsub", a, b));
    long left =
        makeBinary(
            "bvshl",
            FunctionDeclarationKind.BV_SHL,
            getFormulaType(bitvector),
            bitvector,
            remaining,
            (a, b) -> LeanSmtNativeApi.mkApp2("bvshl", a, b));
    return makeBinary(
        "bvor",
        FunctionDeclarationKind.BV_OR,
        getFormulaType(bitvector),
        left,
        right,
        (a, b) -> LeanSmtNativeApi.mkApp2("bvor", a, b));
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

  private static final class IntToBvKey {
    private final int width;
    private final long intTerm;

    private IntToBvKey(int pWidth, long pIntTerm) {
      width = pWidth;
      intTerm = pIntTerm;
    }

    @Override
    public int hashCode() {
      return Objects.hash(width, intTerm);
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj) {
        return true;
      }
      if (!(obj instanceof IntToBvKey)) {
        return false;
      }
      IntToBvKey other = (IntToBvKey) obj;
      return width == other.width && intTerm == other.intTerm;
    }
  }

  private static final class UfApplication {
    private final long handle;
    private final ImmutableList<Long> arguments;

    UfApplication(long pHandle, ImmutableList<Long> pArguments) {
      handle = pHandle;
      arguments = pArguments;
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
