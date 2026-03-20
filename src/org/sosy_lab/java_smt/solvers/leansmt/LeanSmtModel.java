// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import com.google.common.base.Splitter;
import com.google.common.collect.ImmutableList;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

final class LeanSmtModel extends AbstractModel<Long, LeanSmtType, Long> {

  private final LeanSmtFormulaCreator leanCreator;
  private final Map<String, Long> variablesByName;
  private final Map<Long, Value> valuesByHandle;
  private final Set<Long> relevantHandles;

  private static final class Value {
    private final LeanSmtType type;
    private final Object value;

    Value(LeanSmtType pType, Object pValue) {
      type = pType;
      value = pValue;
    }
  }

  private static final class ParsedModelSort {
    private final LeanSmtType type;
    private final int valueStartIndex;

    private ParsedModelSort(LeanSmtType pType, int pValueStartIndex) {
      type = pType;
      valueStartIndex = pValueStartIndex;
    }
  }

  LeanSmtModel(
      LeanSmtTheoremProver pProver,
      LeanSmtFormulaCreator pCreator,
      Map<String, Long> pVariablesByName,
      String pRawModel,
      Set<Long> pRelevantHandles) {
    super(pProver, pCreator);
    leanCreator = pCreator;
    variablesByName = pVariablesByName;
    relevantHandles = Set.copyOf(pRelevantHandles);
    valuesByHandle = indexValuesByHandle(parseModel(pRawModel, pVariablesByName.keySet()));
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    java.util.LinkedHashSet<ValueAssignment> out = new java.util.LinkedHashSet<>();
    for (Map.Entry<Long, Value> e : valuesByHandle.entrySet()) {
      long variableHandle = e.getKey();
      if (!relevantHandles.contains(variableHandle)) {
        continue;
      }
      LeanSmtFormulaCreator.Expr expr = leanCreator.getExpression(variableHandle);
      if (isHiddenHelperVariable(expr)) {
        continue;
      }
      long valueHandle = makeValueFormula(e.getValue());
      long assignmentHandle;
      if (e.getValue().type.isBool() && e.getValue().value instanceof Boolean) {
        assignmentHandle =
            ((Boolean) e.getValue().value)
                ? variableHandle
                : LeanSmtNativeApiResult.not(leanCreator, variableHandle);
      } else {
        assignmentHandle = LeanSmtNativeApiResult.eq(leanCreator, variableHandle, valueHandle);
      }
      out.add(
          new ValueAssignment(
              leanCreator.encapsulateWithTypeOf(variableHandle),
              leanCreator.encapsulateWithTypeOf(valueHandle),
              leanCreator.encapsulateBoolean(assignmentHandle),
              expr.symbol,
              toUserValue(e.getValue()),
              getArgumentInterpretation(expr)));
    }
    return ImmutableList.copyOf(out);
  }

  @Override
  protected @Nullable Long evalImpl(Long pFormula) {
    Value value = evaluateValue(pFormula);
    if (value == null) {
      return null;
    }
    return makeValueFormula(value);
  }

  private @Nullable Value evaluateValue(long handle) {
    Value directValue = valuesByHandle.get(handle);
    if (directValue != null) {
      return directValue;
    }

    LeanSmtFormulaCreator.Expr expr = leanCreator.getExpression(handle);
    switch (expr.kind) {
      case VARIABLE:
        return defaultValue(expr.type);

      case CONSTANT:
        return new Value(LeanSmtFormulaCreator.fromFormulaType(expr.type), expr.constantValue);

      case APPLICATION:
        List<Object> args = new ArrayList<>(expr.arguments.size());
        for (long arg : expr.arguments) {
          Value value = evaluateValue(arg);
          if (value == null) {
            return null;
          }
          args.add(value.value);
        }
        if (expr.declarationKind == FunctionDeclarationKind.UF) {
          return findCongruentUfValue(expr, args);
        }
        Object result = apply(expr, args);
        if (result == null) {
          return null;
        }
        return new Value(LeanSmtFormulaCreator.fromFormulaType(expr.type), result);

      default:
        return null;
    }
  }

  private @Nullable Object apply(LeanSmtFormulaCreator.Expr expr, List<Object> args) {
    String symbol = expr.symbol;
    switch (symbol) {
      case "not":
        return !((Boolean) args.get(0));
      case "and":
        return (Boolean) args.get(0) && (Boolean) args.get(1);
      case "or":
        return (Boolean) args.get(0) || (Boolean) args.get(1);
      case "xor":
        return (Boolean) args.get(0) ^ (Boolean) args.get(1);
      case "=>":
        return !((Boolean) args.get(0)) || (Boolean) args.get(1);
      case "=":
        return args.get(0).equals(args.get(1));
      case "distinct":
        return !args.get(0).equals(args.get(1));
      case "<":
        return compare(args.get(0), args.get(1)) < 0;
      case "<=":
        return compare(args.get(0), args.get(1)) <= 0;
      case ">":
        return compare(args.get(0), args.get(1)) > 0;
      case ">=":
        return compare(args.get(0), args.get(1)) >= 0;
      case "+":
        return add(args.get(0), args.get(1));
      case "-":
        if (args.size() == 1) {
          Object value = args.get(0);
          if (value instanceof BigInteger) {
            return ((BigInteger) value).negate();
          }
          return ((Rational) value).negate();
        }
        return sub(args.get(0), args.get(1));
      case "*":
        return mul(args.get(0), args.get(1));
      case "div":
      case "/":
        return div(args.get(0), args.get(1));
      case "mod":
        return mod(args.get(0), args.get(1));
      case "ite":
        return (Boolean) args.get(0) ? args.get(1) : args.get(2);
      case "floor":
        return floor(args.get(0));
      case "bvnot":
        return bvNot((BigInteger) args.get(0), bitvectorWidth(expr));
      case "bvneg":
        return bvNeg((BigInteger) args.get(0), bitvectorWidth(expr));
      case "bvand":
        return bvAnd((BigInteger) args.get(0), (BigInteger) args.get(1), bitvectorWidth(expr));
      case "bvor":
        return bvOr((BigInteger) args.get(0), (BigInteger) args.get(1), bitvectorWidth(expr));
      case "bvxor":
        return bvXor((BigInteger) args.get(0), (BigInteger) args.get(1), bitvectorWidth(expr));
      case "bvadd":
        return bvAdd((BigInteger) args.get(0), (BigInteger) args.get(1), bitvectorWidth(expr));
      case "bvsub":
        return bvSub((BigInteger) args.get(0), (BigInteger) args.get(1), bitvectorWidth(expr));
      case "bvmul":
        return bvMul((BigInteger) args.get(0), (BigInteger) args.get(1), bitvectorWidth(expr));
      case "ubv_to_int":
        return bvNormalize((BigInteger) args.get(0), bitvectorWidthOfArgument(expr, 0));
      case "sbv_to_int":
        return bvToSignedInteger((BigInteger) args.get(0), bitvectorWidthOfArgument(expr, 0));
      case "rotate_left":
        return bvRotateLeft(
            (BigInteger) args.get(0), (BigInteger) args.get(1), bitvectorWidth(expr));
      case "rotate_right":
        return bvRotateRight(
            (BigInteger) args.get(0), (BigInteger) args.get(1), bitvectorWidth(expr));
      default:
        if (symbol.startsWith("(_ extract ") && symbol.endsWith(")")) {
          return bvExtract((BigInteger) args.get(0), symbol, bitvectorWidth(expr));
        }
        if (symbol.startsWith("(_ int_to_bv ") || symbol.startsWith("(_ int2bv ")) {
          int width = parseIndexedUnaryParameter(symbol);
          if (width != bitvectorWidth(expr)) {
            throw new IllegalArgumentException(
                "Mismatched int_to_bv width: symbol width "
                    + width
                    + ", expression width "
                    + bitvectorWidth(expr));
          }
          return bvNormalize((BigInteger) args.get(0), width);
        }
        if (symbol.startsWith("(_ zero_extend ") || symbol.startsWith("(_ sign_extend ")) {
          return evaluateIndexedExtend(expr, symbol, args);
        }
        if (symbol.startsWith("(_ rotate_left ")) {
          return evaluateIndexedRotate(expr, symbol, args, /* rotateLeft= */ true);
        }
        if (symbol.startsWith("(_ rotate_right ")) {
          return evaluateIndexedRotate(expr, symbol, args, /* rotateLeft= */ false);
        }
        return null;
    }
  }

  private @Nullable Object evaluateIndexedExtend(
      LeanSmtFormulaCreator.Expr expr, String symbol, List<Object> args) {
    if (args.size() != 1 || !(args.get(0) instanceof BigInteger)) {
      return null;
    }
    int extension = parseIndexedUnaryParameter(symbol);
    int inWidth = bitvectorWidthOfArgument(expr, 0);
    int outWidth = bitvectorWidth(expr);
    if (inWidth + extension != outWidth) {
      throw new IllegalArgumentException(
          "Mismatched extend width: input width "
              + inWidth
              + ", extension "
              + extension
              + ", output width "
              + outWidth);
    }
    BigInteger value = (BigInteger) args.get(0);
    if (symbol.startsWith("(_ zero_extend ")) {
      return bvNormalize(value, outWidth);
    }
    return bvNormalize(bvToSignedInteger(value, inWidth), outWidth);
  }

  private static @Nullable Object evaluateIndexedRotate(
      LeanSmtFormulaCreator.Expr expr, String symbol, List<Object> args, boolean rotateLeft) {
    if (args.size() != 1 || !(args.get(0) instanceof BigInteger)) {
      return null;
    }
    int rotation = parseIndexedUnaryParameter(symbol);
    int width = bitvectorWidth(expr);
    BigInteger value = (BigInteger) args.get(0);
    return rotateLeft
        ? bvRotateLeft(value, BigInteger.valueOf(rotation), width)
        : bvRotateRight(value, BigInteger.valueOf(rotation), width);
  }

  // Kept for backwards-compatible tests that invoke this helper reflectively.
  @SuppressWarnings("unused")
  private static @Nullable Object apply(String symbol, List<Object> args) {
    switch (symbol) {
      case "not":
        return !((Boolean) args.get(0));
      case "and":
        return (Boolean) args.get(0) && (Boolean) args.get(1);
      case "or":
        return (Boolean) args.get(0) || (Boolean) args.get(1);
      case "xor":
        return (Boolean) args.get(0) ^ (Boolean) args.get(1);
      case "=>":
        return !((Boolean) args.get(0)) || (Boolean) args.get(1);
      case "=":
        return args.get(0).equals(args.get(1));
      case "distinct":
        return !args.get(0).equals(args.get(1));
      case "<":
        return compare(args.get(0), args.get(1)) < 0;
      case "<=":
        return compare(args.get(0), args.get(1)) <= 0;
      case ">":
        return compare(args.get(0), args.get(1)) > 0;
      case ">=":
        return compare(args.get(0), args.get(1)) >= 0;
      case "+":
        return add(args.get(0), args.get(1));
      case "-":
        if (args.size() == 1) {
          Object value = args.get(0);
          if (value instanceof BigInteger) {
            return ((BigInteger) value).negate();
          }
          return ((Rational) value).negate();
        }
        return sub(args.get(0), args.get(1));
      case "*":
        return mul(args.get(0), args.get(1));
      case "div":
      case "/":
        return div(args.get(0), args.get(1));
      case "mod":
        return mod(args.get(0), args.get(1));
      case "ite":
        return (Boolean) args.get(0) ? args.get(1) : args.get(2);
      case "floor":
        return floor(args.get(0));
      default:
        return null;
    }
  }

  private static int bitvectorWidth(LeanSmtFormulaCreator.Expr expr) {
    if (!(expr.type instanceof FormulaType.BitvectorType)) {
      throw new IllegalArgumentException(
          "Expected bitvector-typed expression for '" + expr.symbol + "', got " + expr.type);
    }
    return ((FormulaType.BitvectorType) expr.type).getSize();
  }

  private int bitvectorWidthOfArgument(LeanSmtFormulaCreator.Expr expr, int argIndex) {
    return bitvectorWidth(leanCreator.getExpression(expr.arguments.get(argIndex)));
  }

  private static BigInteger bvNormalize(BigInteger value, int width) {
    BigInteger modulus = BigInteger.ONE.shiftLeft(width);
    BigInteger normalized = value.mod(modulus);
    if (normalized.signum() < 0) {
      normalized = normalized.add(modulus);
    }
    return normalized;
  }

  private static BigInteger bvNot(BigInteger value, int width) {
    BigInteger mask = BigInteger.ONE.shiftLeft(width).subtract(BigInteger.ONE);
    return value.xor(mask).and(mask);
  }

  private static BigInteger bvNeg(BigInteger value, int width) {
    return bvNormalize(value.negate(), width);
  }

  private static BigInteger bvAnd(BigInteger a, BigInteger b, int width) {
    BigInteger mask = BigInteger.ONE.shiftLeft(width).subtract(BigInteger.ONE);
    return a.and(b).and(mask);
  }

  private static BigInteger bvOr(BigInteger a, BigInteger b, int width) {
    BigInteger mask = BigInteger.ONE.shiftLeft(width).subtract(BigInteger.ONE);
    return a.or(b).and(mask);
  }

  private static BigInteger bvXor(BigInteger a, BigInteger b, int width) {
    BigInteger mask = BigInteger.ONE.shiftLeft(width).subtract(BigInteger.ONE);
    return a.xor(b).and(mask);
  }

  private static BigInteger bvAdd(BigInteger a, BigInteger b, int width) {
    return bvNormalize(a.add(b), width);
  }

  private static BigInteger bvSub(BigInteger a, BigInteger b, int width) {
    return bvNormalize(a.subtract(b), width);
  }

  private static BigInteger bvMul(BigInteger a, BigInteger b, int width) {
    return bvNormalize(a.multiply(b), width);
  }

  private static BigInteger bvExtract(BigInteger value, String symbol, int resultWidth) {
    List<String> parts =
        Splitter.onPattern("\\s+").omitEmptyStrings().splitToList(symbol.substring(1, symbol.length() - 1).trim());
    if (parts.size() != 4 || !"_".equals(parts.get(0)) || !"extract".equals(parts.get(1))) {
      throw new IllegalArgumentException("Unsupported extract symbol: " + symbol);
    }
    int lsb = Integer.parseInt(parts.get(3));
    BigInteger shifted = value.shiftRight(lsb);
    return shifted.and(BigInteger.ONE.shiftLeft(resultWidth).subtract(BigInteger.ONE));
  }

  private static int parseIndexedUnaryParameter(String symbol) {
    List<String> parts =
        Splitter.onPattern("\\s+").omitEmptyStrings().splitToList(symbol.substring(1, symbol.length() - 1).trim());
    if (parts.size() != 3 || !"_".equals(parts.get(0))) {
      throw new IllegalArgumentException("Unsupported indexed symbol: " + symbol);
    }
    try {
      int value = Integer.parseInt(parts.get(2));
      if (value < 0) {
        throw new IllegalArgumentException("Indexed symbol must use non-negative indices: " + symbol);
      }
      return value;
    } catch (NumberFormatException e) {
      throw new IllegalArgumentException("Invalid indexed numeral in symbol: " + symbol, e);
    }
  }

  private static BigInteger bvToSignedInteger(BigInteger value, int width) {
    BigInteger normalized = bvNormalize(value, width);
    if (width <= 0) {
      return normalized;
    }
    BigInteger signBit = BigInteger.ONE.shiftLeft(width - 1);
    if (normalized.and(signBit).equals(BigInteger.ZERO)) {
      return normalized;
    }
    return normalized.subtract(BigInteger.ONE.shiftLeft(width));
  }

  private static BigInteger bvRotateLeft(BigInteger value, BigInteger shiftValue, int width) {
    BigInteger normalized = bvNormalize(value, width);
    if (width == 0) {
      return normalized;
    }
    int shift = shiftValue.mod(BigInteger.valueOf(width)).intValue();
    if (shift == 0) {
      return normalized;
    }
    BigInteger mask = BigInteger.ONE.shiftLeft(width).subtract(BigInteger.ONE);
    BigInteger left = normalized.shiftLeft(shift).and(mask);
    BigInteger right = normalized.shiftRight(width - shift);
    return left.or(right).and(mask);
  }

  private static BigInteger bvRotateRight(BigInteger value, BigInteger shiftValue, int width) {
    BigInteger normalized = bvNormalize(value, width);
    if (width == 0) {
      return normalized;
    }
    int shift = shiftValue.mod(BigInteger.valueOf(width)).intValue();
    if (shift == 0) {
      return normalized;
    }
    BigInteger mask = BigInteger.ONE.shiftLeft(width).subtract(BigInteger.ONE);
    BigInteger right = normalized.shiftRight(shift);
    BigInteger left = normalized.shiftLeft(width - shift).and(mask);
    return left.or(right).and(mask);
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

  private Map<Long, Value> indexValuesByHandle(Map<String, Value> parsedValues) {
    Map<Long, Value> out = new LinkedHashMap<>();
    for (Map.Entry<String, Value> entry : parsedValues.entrySet()) {
      Long handle = variablesByName.get(entry.getKey());
      if (handle != null) {
        out.put(handle, entry.getValue());
      }
    }
    return out;
  }

  private static Map<String, Value> parseModel(
      String rawModel, java.util.Collection<String> knownIdentifiers) {
    LinkedHashMap<String, Value> out = new LinkedHashMap<>();
    for (String definition : splitTopLevelDefinitions(rawModel)) {
      List<String> tokens = tokenizeSExpr(definition);
      if (tokens.size() < 7) {
        continue;
      }
      if (!"(".equals(tokens.get(0)) || !"define-fun".equals(tokens.get(1))) {
        continue;
      }
      if (!"(".equals(tokens.get(3)) || !")".equals(tokens.get(4))) {
        continue;
      }

      String name = resolveModelIdentifier(decodeIdentifier(tokens.get(2)), knownIdentifiers);
      ParsedModelSort parsedSort = parseModelSort(tokens, 5);
      if (parsedSort == null) {
        continue;
      }
      List<String> valueTokens = tokens.subList(parsedSort.valueStartIndex, tokens.size() - 1);
      if (parsedSort.type.isBool()) {
        if (valueTokens.size() == 1 && ("true".equals(valueTokens.get(0)) || "false".equals(valueTokens.get(0)))) {
          out.put(name, new Value(LeanSmtType.BOOL, Boolean.parseBoolean(valueTokens.get(0))));
        }
      } else if (parsedSort.type.isInt()) {
        out.put(name, new Value(LeanSmtType.INT, parseBigIntExpr(valueTokens)));
      } else if (parsedSort.type.isReal()) {
        out.put(name, new Value(LeanSmtType.REAL, parseRationalExpr(valueTokens)));
      } else if (parsedSort.type.isBitvector()) {
        out.put(
            name,
            new Value(
                parsedSort.type, parseBitvectorExpr(valueTokens, parsedSort.type.getBitvectorSize())));
      }
    }
    return out;
  }

  private static String resolveModelIdentifier(
      String name, java.util.Collection<String> knownIdentifiers) {
    if (knownIdentifiers.contains(name)) {
      return name;
    }
    if (name.length() >= 2 && name.startsWith("_") && name.endsWith("_")) {
      String inner = name.substring(1, name.length() - 1);
      if (knownIdentifiers.contains(inner)) {
        return inner;
      }
    }
    return name;
  }

  private static @Nullable ParsedModelSort parseModelSort(List<String> tokens, int startIndex) {
    if (startIndex >= tokens.size() - 1) {
      return null;
    }
    String token = tokens.get(startIndex);
    if ("Bool".equals(token)) {
      return new ParsedModelSort(LeanSmtType.BOOL, startIndex + 1);
    }
    if ("Int".equals(token)) {
      return new ParsedModelSort(LeanSmtType.INT, startIndex + 1);
    }
    if ("Real".equals(token)) {
      return new ParsedModelSort(LeanSmtType.REAL, startIndex + 1);
    }
    if ("(".equals(token)
        && startIndex + 4 < tokens.size()
        && "_".equals(tokens.get(startIndex + 1))
        && "BitVec".equals(tokens.get(startIndex + 2))
        && ")".equals(tokens.get(startIndex + 4))) {
      try {
        int width = Integer.parseInt(tokens.get(startIndex + 3));
        if (width <= 0) {
          return null;
        }
        return new ParsedModelSort(LeanSmtType.bitvector(width), startIndex + 5);
      } catch (NumberFormatException e) {
        return null;
      }
    }
    return null;
  }

  private static List<String> splitTopLevelDefinitions(String rawModel) {
    List<String> defs = new ArrayList<>();
    for (int i = 0; i < rawModel.length(); i++) {
      char c = rawModel.charAt(i);
      if (c == '(') {
        int commandStart = i + 1;
        while (commandStart < rawModel.length()
            && Character.isWhitespace(rawModel.charAt(commandStart))) {
          commandStart++;
        }
        if (!rawModel.startsWith("define-fun", commandStart)) {
          continue;
        }

        int depth = 1;
        int end = i + 1;
        boolean inQuotedIdentifier = false;
        while (end < rawModel.length() && depth > 0) {
          char ch = rawModel.charAt(end);
          if (inQuotedIdentifier) {
            if (ch == '|') {
              if (end + 1 < rawModel.length() && rawModel.charAt(end + 1) == '|') {
                end++;
              } else {
                inQuotedIdentifier = false;
              }
            }
          } else if (ch == '|') {
            inQuotedIdentifier = true;
          } else if (ch == '(') {
            depth++;
          } else if (ch == ')') {
            depth--;
          }
          end++;
        }
        if (depth == 0) {
          defs.add(rawModel.substring(i, end).trim());
          i = end - 1;
        }
      }
    }
    return defs;
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
      throw new IllegalArgumentException("Unsupported Real model expression: " + String.join(" ", tokens));
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
    } else {
      throw new IllegalArgumentException("Unsupported Real operator in model expression: " + op);
    }
  }

  @SuppressWarnings("unused")
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

  private static String requireToken(Deque<String> queue, String expected) {
    String token = queue.pollFirst();
    if (token == null) {
      throw new IllegalArgumentException("Unexpected end of model expression, expected " + expected);
    }
    if (")".equals(expected) && !")".equals(token)) {
      throw new IllegalArgumentException("Expected ')', got '" + token + "'");
    }
    return token;
  }

  private static boolean isDecimalLike(String token) {
    return token.contains(".") || token.contains("e") || token.contains("E");
  }

  private static String decodeIdentifier(String token) {
    if (token.length() >= 2 && token.startsWith("|") && token.endsWith("|")) {
      return token.substring(1, token.length() - 1).replace("||", "|");
    }
    return token;
  }

  private static Value defaultValue(FormulaType<?> type) {
    LeanSmtType leanType = LeanSmtFormulaCreator.fromFormulaType(type);
    if (leanType.isBool()) {
      return new Value(leanType, false);
    }
    if (leanType.isInt()) {
      return new Value(leanType, BigInteger.ZERO);
    }
    if (leanType.isReal()) {
      return new Value(leanType, Rational.ofBigInteger(BigInteger.ZERO));
    }
    if (leanType.isBitvector()) {
      return new Value(leanType, BigInteger.ZERO);
    }
    throw new AssertionError("Unexpected LeanSMT type " + leanType);
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

  private List<Object> getArgumentInterpretation(LeanSmtFormulaCreator.Expr expr) {
    if (expr.declarationKind != FunctionDeclarationKind.UF) {
      return List.of();
    }
    List<Object> out = new ArrayList<>(expr.arguments.size());
    for (long arg : expr.arguments) {
      Value value = evaluateValue(arg);
      if (value == null) {
        return List.of();
      }
      out.add(toUserValue(value));
    }
    return out;
  }

  private static boolean isHiddenHelperVariable(LeanSmtFormulaCreator.Expr expr) {
    return expr.kind == LeanSmtFormulaCreator.ExprKind.VARIABLE
        && (expr.symbol.startsWith("__floor#")
            || expr.symbol.startsWith("__int2bv#")
            || expr.symbol.startsWith("__ratc#"));
  }

  private @Nullable Value findCongruentUfValue(
      LeanSmtFormulaCreator.Expr expr, List<Object> interpretedArgs) {
    for (Map.Entry<Long, Value> entry : valuesByHandle.entrySet()) {
      LeanSmtFormulaCreator.Expr candidate = leanCreator.getExpression(entry.getKey());
      if (candidate.declarationKind != FunctionDeclarationKind.UF
          || !candidate.symbol.equals(expr.symbol)
          || candidate.arguments.size() != expr.arguments.size()) {
        continue;
      }
      List<Object> candidateArgs = new ArrayList<>(candidate.arguments.size());
      boolean known = true;
      for (long argHandle : candidate.arguments) {
        Value candidateArgValue = evaluateValue(argHandle);
        if (candidateArgValue == null) {
          known = false;
          break;
        }
        candidateArgs.add(candidateArgValue.value);
      }
      if (known && candidateArgs.equals(interpretedArgs)) {
        return entry.getValue();
      }
    }
    return null;
  }

  private static int compare(Object a, Object b) {
    if (a instanceof BigInteger && b instanceof BigInteger) {
      return ((BigInteger) a).compareTo((BigInteger) b);
    }
    return toRational(a).compareTo(toRational(b));
  }

  private static Object add(Object a, Object b) {
    if (a instanceof BigInteger && b instanceof BigInteger) {
      return ((BigInteger) a).add((BigInteger) b);
    }
    return toRational(a).plus(toRational(b));
  }

  private static Object sub(Object a, Object b) {
    if (a instanceof BigInteger && b instanceof BigInteger) {
      return ((BigInteger) a).subtract((BigInteger) b);
    }
    return toRational(a).minus(toRational(b));
  }

  private static Object mul(Object a, Object b) {
    if (a instanceof BigInteger && b instanceof BigInteger) {
      return ((BigInteger) a).multiply((BigInteger) b);
    }
    return toRational(a).times(toRational(b));
  }

  private static Object div(Object a, Object b) {
    if (a instanceof BigInteger && b instanceof BigInteger) {
      return euclideanDivMod((BigInteger) a, (BigInteger) b)[0];
    }
    return toRational(a).divides(toRational(b));
  }

  private static Object mod(Object a, Object b) {
    return euclideanDivMod((BigInteger) a, (BigInteger) b)[1];
  }

  private static BigInteger[] euclideanDivMod(BigInteger dividend, BigInteger divisor) {
    BigInteger quotient = dividend.divide(divisor);
    BigInteger remainder = dividend.remainder(divisor);
    if (remainder.signum() >= 0) {
      return new BigInteger[] {quotient, remainder};
    }

    BigInteger absDivisor = divisor.abs();
    BigInteger adjustedQuotient =
        divisor.signum() > 0 ? quotient.subtract(BigInteger.ONE) : quotient.add(BigInteger.ONE);
    BigInteger adjustedRemainder = remainder.add(absDivisor);
    return new BigInteger[] {adjustedQuotient, adjustedRemainder};
  }

  private static Rational toRational(Object a) {
    if (a instanceof Rational) {
      return (Rational) a;
    }
    return Rational.ofBigInteger((BigInteger) a);
  }

  private static BigInteger floor(Object a) {
    if (a instanceof BigInteger) {
      return (BigInteger) a;
    }
    Rational r = (Rational) a;
    BigInteger num = r.getNum();
    BigInteger den = r.getDen();
    if (den.signum() < 0) {
      num = num.negate();
      den = den.negate();
    }
    if (num.signum() >= 0) {
      return num.divide(den);
    }
    return num.negate().add(den).subtract(BigInteger.ONE).divide(den).negate();
  }

  private static final class LeanSmtNativeApiResult {
    private LeanSmtNativeApiResult() {}

    static long eq(LeanSmtFormulaCreator creator, long a, long b) {
      return creator.makeBinary("=", org.sosy_lab.java_smt.api.FunctionDeclarationKind.EQ, org.sosy_lab.java_smt.api.FormulaType.BooleanType, a, b, LeanSmtNativeApi::mkEq);
    }

    static long not(LeanSmtFormulaCreator creator, long a) {
      return creator.makeUnary("not", org.sosy_lab.java_smt.api.FunctionDeclarationKind.NOT, org.sosy_lab.java_smt.api.FormulaType.BooleanType, a, LeanSmtNativeApi::mkNot);
    }
  }
}
