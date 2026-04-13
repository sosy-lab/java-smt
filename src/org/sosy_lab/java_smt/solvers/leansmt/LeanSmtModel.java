// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import com.google.common.collect.ImmutableList;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

final class LeanSmtModel extends AbstractModel<Long, LeanSmtType, Long> {

  private final LeanSmtFormulaCreator leanCreator;
  private final LeanSmtSmtLibPrinter printer;
  private final long solver;
  private final ImmutableList<ValueAssignment> modelAssignments;
  private final Map<Long, @Nullable Value> valuesByHandle = new LinkedHashMap<>();

  private static final class Value {
    private final LeanSmtType type;
    private final Object value;

    Value(LeanSmtType pType, Object pValue) {
      type = pType;
      value = pValue;
    }
  }

  LeanSmtModel(
      LeanSmtTheoremProver pProver,
      LeanSmtFormulaCreator pCreator,
      long pSolver,
      Set<Long> pRelevantHandles) {
    super(pProver, pCreator);
    leanCreator = pCreator;
    printer = new LeanSmtSmtLibPrinter(pCreator, true);
    solver = pSolver;
    modelAssignments = generateModelAssignments(pRelevantHandles);
  }

  @Override
  public void close() {
    if (!isClosed()) {
      LeanSmtNativeApi.deleteSolverBestEffort(solver);
    }
    super.close();
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return modelAssignments;
  }

  @Override
  protected @Nullable Long evalImpl(Long pFormula) {
    Value value = getValue(pFormula);
    return value == null ? null : makeValueFormula(value);
  }

  private ImmutableList<ValueAssignment> generateModelAssignments(Iterable<Long> relevantHandles) {
    LinkedHashSet<ValueAssignment> out = new LinkedHashSet<>();
    for (long handle : relevantHandles) {
      LeanSmtFormulaCreator.Expr expr = leanCreator.getExpression(handle);
      if (!isAssignmentTarget(expr)) {
        continue;
      }

      Value value = getValue(handle);
      if (value == null) {
        continue;
      }

      long valueHandle = makeValueFormula(value);
      long assignmentHandle;
      if (value.type.isBool() && value.value instanceof Boolean) {
        assignmentHandle =
            ((Boolean) value.value) ? handle : LeanSmtNativeApiResult.not(leanCreator, handle);
      } else {
        assignmentHandle = LeanSmtNativeApiResult.eq(leanCreator, handle, valueHandle);
      }

      out.add(
          new ValueAssignment(
              leanCreator.encapsulateWithTypeOf(handle),
              leanCreator.encapsulateWithTypeOf(valueHandle),
              leanCreator.encapsulateBoolean(assignmentHandle),
              expr.symbol,
              toUserValue(value),
              getArgumentInterpretation(expr)));
    }
    return ImmutableList.copyOf(out);
  }

  private @Nullable Value getValue(long handle) {
    if (valuesByHandle.containsKey(handle)) {
      return valuesByHandle.get(handle);
    }

    @Nullable Value value = null;
    try {
      value = parseValue(handle, LeanSmtNativeApi.getValueSmtLib(solver, printer.dumpTerm(handle)));
    } catch (IllegalArgumentException | SolverException e) {
      value = null;
    }
    valuesByHandle.put(handle, value);
    return value;
  }

  private @Nullable Value parseValue(long handle, String rawValue) {
    LeanSmtFormulaCreator.Expr expr = leanCreator.getExpression(handle);
    LeanSmtType type = LeanSmtFormulaCreator.fromFormulaType(expr.type);
    ImmutableList<String> tokens = tokenizeSExpr(rawValue);

    if (type.isBool()) {
      if (tokens.size() == 1 && ("true".equals(tokens.get(0)) || "false".equals(tokens.get(0)))) {
        return new Value(type, Boolean.parseBoolean(tokens.get(0)));
      }
      return null;
    }
    if (type.isInt()) {
      return new Value(type, parseBigIntExpr(tokens));
    }
    if (type.isReal()) {
      return new Value(type, parseRationalExpr(tokens));
    }
    if (type.isBitvector()) {
      return new Value(type, parseBitvectorExpr(tokens, type.getBitvectorSize()));
    }
    return null;
  }

  private long makeValueFormula(Value v) {
    if (v.type.isBool()) {
      return ((Boolean) v.value) ? leanCreator.getTrueHandle() : leanCreator.getFalseHandle();
    }
    if (v.type.isInt()) {
      return leanCreator.makeIntConstant((BigInteger) v.value);
    }
    if (v.type.isReal()) {
      return leanCreator.makeRealConstant((Rational) v.value);
    }
    if (v.type.isBitvector()) {
      return leanCreator.makeBitvectorConstant(v.type.getBitvectorSize(), (BigInteger) v.value);
    }
    throw new AssertionError("Unexpected LeanSMT type " + v.type);
  }

  private List<Object> getArgumentInterpretation(LeanSmtFormulaCreator.Expr expr) {
    if (expr.declarationKind != FunctionDeclarationKind.UF) {
      return List.of();
    }

    List<Object> out = new ArrayList<>(expr.arguments.size());
    for (long arg : expr.arguments) {
      Value value = getValue(arg);
      if (value == null) {
        return List.of();
      }
      out.add(toUserValue(value));
    }
    return out;
  }

  private static boolean isAssignmentTarget(LeanSmtFormulaCreator.Expr expr) {
    return expr.kind == LeanSmtFormulaCreator.ExprKind.VARIABLE
        || expr.declarationKind == FunctionDeclarationKind.UF;
  }

  private static Object toUserValue(Value value) {
    if (value.value instanceof Rational) {
      Rational rational = (Rational) value.value;
      if (rational.getDen().equals(BigInteger.ONE)) {
        return rational.getNum();
      }
    }
    return value.value;
  }

  private static ImmutableList<String> tokenizeSExpr(String expr) {
    if (expr.isEmpty()) {
      return ImmutableList.of();
    }
    ImmutableList.Builder<String> tokens = ImmutableList.builder();
    StringBuilder current = new StringBuilder();
    boolean inQuotedIdentifier = false;
    for (int i = 0; i < expr.length(); i++) {
      char c = expr.charAt(i);

      if (inQuotedIdentifier) {
        current.append(c);
        if (c == '|') {
          if (i + 1 < expr.length() && expr.charAt(i + 1) == '|') {
            current.append('|');
            i++;
          } else {
            tokens.add(current.toString());
            current.setLength(0);
            inQuotedIdentifier = false;
          }
        }
        continue;
      }

      if (c == '|') {
        if (current.length() > 0) {
          tokens.add(current.toString());
          current.setLength(0);
        }
        current.append(c);
        inQuotedIdentifier = true;
      } else if (c == '(' || c == ')') {
        if (current.length() > 0) {
          tokens.add(current.toString());
          current.setLength(0);
        }
        tokens.add(Character.toString(c));
      } else if (Character.isWhitespace(c)) {
        if (current.length() > 0) {
          tokens.add(current.toString());
          current.setLength(0);
        }
      } else {
        current.append(c);
      }
    }
    if (inQuotedIdentifier) {
      throw new IllegalArgumentException(
          "Unterminated quoted identifier in model expression: " + expr);
    }
    if (current.length() > 0) {
      tokens.add(current.toString());
    }
    return tokens.build();
  }

  private static BigInteger parseBigIntExpr(List<String> tokens) {
    if (tokens.isEmpty()) {
      throw new IllegalArgumentException("Unsupported Int model expression: <empty>");
    }

    Deque<String> queue = new ArrayDeque<>(tokens);
    BigInteger value = parseBigIntTerm(queue);
    if (!queue.isEmpty()) {
      throw new IllegalArgumentException(
          "Unsupported Int model expression: " + String.join(" ", tokens));
    }
    return value;
  }

  private static BigInteger parseBigIntTerm(Deque<String> queue) {
    String token = queue.pollFirst();
    if (token == null) {
      throw new IllegalArgumentException("Unexpected end of Int model expression");
    }
    if (!"(".equals(token)) {
      return new BigInteger(token);
    }

    String op = requireToken(queue, "operator");
    if ("-".equals(op) || "+".equals(op)) {
      BigInteger inner = parseBigIntTerm(queue);
      requireToken(queue, ")");
      return "-".equals(op) ? inner.negate() : inner;
    }
    throw new IllegalArgumentException("Unsupported Int model operator: " + op);
  }

  private static Rational parseRationalExpr(List<String> tokens) {
    if (tokens.size() == 1) {
      String atom = tokens.get(0);
      if (isDecimalLike(atom)) {
        return Rational.ofBigDecimal(new BigDecimal(atom));
      }
      return Rational.ofString(atom);
    }

    Deque<String> queue = new ArrayDeque<>(tokens);
    Rational value = parseRationalTerm(queue);
    if (!queue.isEmpty()) {
      throw new IllegalArgumentException(
          "Unsupported Real model expression: " + String.join(" ", tokens));
    }
    return value;
  }

  private static Rational parseRationalTerm(Deque<String> queue) {
    String token = queue.pollFirst();
    if (token == null) {
      throw new IllegalArgumentException("Unexpected end of model expression");
    }
    if (!"(".equals(token)) {
      if (isDecimalLike(token)) {
        return Rational.ofBigDecimal(new BigDecimal(token));
      }
      return Rational.ofString(token);
    }

    String op = requireToken(queue, "operator");
    if ("-".equals(op) || "+".equals(op)) {
      Rational inner = parseRationalTerm(queue);
      requireToken(queue, ")");
      return "-".equals(op) ? inner.negate() : inner;
    } else if ("/".equals(op)) {
      Rational num = parseRationalTerm(queue);
      Rational den = parseRationalTerm(queue);
      requireToken(queue, ")");
      return num.divides(den);
    }
    throw new IllegalArgumentException("Unsupported Real operator in model expression: " + op);
  }

  private static BigInteger parseBitvectorExpr(List<String> tokens, int width) {
    if (tokens.isEmpty()) {
      throw new IllegalArgumentException("Unsupported bitvector model expression: <empty>");
    }
    if (tokens.size() == 1) {
      String token = tokens.get(0);
      BigInteger value;
      if (token.startsWith("#b")) {
        value = new BigInteger(token.substring(2), 2);
      } else if (token.startsWith("#x")) {
        value = new BigInteger(token.substring(2), 16);
      } else {
        value = new BigInteger(token);
      }
      return bvNormalize(value, width);
    }
    if (tokens.size() == 5
        && "(".equals(tokens.get(0))
        && "_".equals(tokens.get(1))
        && tokens.get(2).startsWith("bv")
        && ")".equals(tokens.get(4))) {
      int encodedWidth = Integer.parseInt(tokens.get(3));
      if (encodedWidth != width) {
        throw new IllegalArgumentException(
            "Bitvector width mismatch in model: expected " + width + ", got " + encodedWidth);
      }
      return bvNormalize(new BigInteger(tokens.get(2).substring(2)), width);
    }
    throw new IllegalArgumentException(
        "Unsupported bitvector model expression: " + String.join(" ", tokens));
  }

  private static BigInteger bvNormalize(BigInteger value, int width) {
    BigInteger modulus = BigInteger.ONE.shiftLeft(width);
    BigInteger normalized = value.mod(modulus);
    if (normalized.signum() < 0) {
      normalized = normalized.add(modulus);
    }
    return normalized;
  }

  private static String requireToken(Deque<String> queue, String expected) {
    String token = queue.pollFirst();
    if (token == null) {
      throw new IllegalArgumentException(
          "Unexpected end of model expression, expected " + expected);
    }
    if (")".equals(expected) && !")".equals(token)) {
      throw new IllegalArgumentException("Expected ')', got '" + token + "'");
    }
    return token;
  }

  private static boolean isDecimalLike(String token) {
    return token.contains(".") || token.contains("e") || token.contains("E");
  }

  private static final class LeanSmtNativeApiResult {
    private LeanSmtNativeApiResult() {}

    static long eq(LeanSmtFormulaCreator creator, long a, long b) {
      return creator.makeBinary("=", FunctionDeclarationKind.EQ, FormulaType.BooleanType, a, b);
    }

    static long not(LeanSmtFormulaCreator creator, long a) {
      return creator.makeUnary("not", FunctionDeclarationKind.NOT, FormulaType.BooleanType, a);
    }
  }
}
