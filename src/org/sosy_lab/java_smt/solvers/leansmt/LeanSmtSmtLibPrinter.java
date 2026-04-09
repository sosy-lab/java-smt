// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** SMT-LIB serializer for the LeanSMT backend's local expression graph. */
final class LeanSmtSmtLibPrinter {

  private final LeanSmtFormulaCreator creator;

  LeanSmtSmtLibPrinter(LeanSmtFormulaCreator pCreator) {
    creator = pCreator;
  }

  String dumpFormula(long formula) throws IOException {
    Map<String, LeanSmtType> variableDecls = new LinkedHashMap<>();
    Set<String> functionDecls = new LinkedHashSet<>();
    collectDeclarations(formula, variableDecls, functionDecls);

    StringBuilder out = new StringBuilder();
    for (Map.Entry<String, LeanSmtType> decl : variableDecls.entrySet()) {
      out.append("(declare-fun ")
          .append(quoteIdentifier(decl.getKey()))
          .append(" () ")
          .append(printSort(decl.getValue()))
          .append(")\n");
    }
    for (String decl : functionDecls) {
      out.append(decl).append('\n');
    }
    out.append("(assert ").append(serializeTerm(formula)).append(')');
    return out.toString();
  }

  private String serializeTerm(long formula) throws IOException {
    return serializeWithLets(formula);
  }

  private String serializeWithLets(long root) {
    Map<Long, Integer> counts = new LinkedHashMap<>();
    countOccurrences(root, counts);

    List<Long> candidates = new ArrayList<>();
    collectOrder(root, counts, candidates, new LinkedHashSet<>());
    if (candidates.isEmpty()) {
      return serialize(root, Map.of());
    }

    Map<Long, String> substitutions = new LinkedHashMap<>();
    int idx = 0;
    for (Long candidate : candidates) {
      substitutions.put(candidate, "$cse" + idx++);
    }

    String body = serialize(root, substitutions);
    for (int i = candidates.size() - 1; i >= 0; i--) {
      long handle = candidates.get(i);
      String name = substitutions.get(handle);

      Map<Long, String> rhsSubs = new LinkedHashMap<>();
      for (int j = 0; j < i; j++) {
        long dependency = candidates.get(j);
        rhsSubs.put(dependency, substitutions.get(dependency));
      }
      body = "(let ((" + name + " " + serialize(handle, rhsSubs) + ")) " + body + ")";
    }
    return body;
  }

  private void countOccurrences(long handle, Map<Long, Integer> counts) {
    counts.put(handle, counts.getOrDefault(handle, 0) + 1);
    LeanSmtFormulaCreator.Expr expr = creator.getExpression(handle);
    if (expr.kind == LeanSmtFormulaCreator.ExprKind.APPLICATION) {
      for (Long arg : expr.arguments) {
        countOccurrences(arg, counts);
      }
    }
  }

  private void collectOrder(
      long handle, Map<Long, Integer> counts, List<Long> out, Set<Long> seen) {
    if (!seen.add(handle)) {
      return;
    }
    LeanSmtFormulaCreator.Expr expr = creator.getExpression(handle);
    if (expr.kind == LeanSmtFormulaCreator.ExprKind.APPLICATION) {
      for (Long arg : expr.arguments) {
        collectOrder(arg, counts, out, seen);
      }
      if (counts.getOrDefault(handle, 0) > 1) {
        out.add(handle);
      }
    }
  }

  private void collectDeclarations(
      long root, Map<String, LeanSmtType> variableDecls, Set<String> functionDecls) {
    Deque<Long> work = new ArrayDeque<>();
    Set<Long> seen = new LinkedHashSet<>();
    work.add(root);

    while (!work.isEmpty()) {
      long handle = work.removeLast();
      if (!seen.add(handle)) {
        continue;
      }
      LeanSmtFormulaCreator.Expr expr = creator.getExpression(handle);
      switch (expr.kind) {
        case VARIABLE:
          variableDecls.putIfAbsent(expr.symbol, LeanSmtFormulaCreator.fromFormulaType(expr.type));
          break;
        case APPLICATION:
          if (expr.declarationKind == org.sosy_lab.java_smt.api.FunctionDeclarationKind.UF) {
            List<String> argSorts = new ArrayList<>(expr.arguments.size());
            for (Long arg : expr.arguments) {
              argSorts.add(
                  printSort(LeanSmtFormulaCreator.fromFormulaType(creator.getFormulaType(arg))));
              work.add(arg);
            }
            StringBuilder decl = new StringBuilder();
            decl.append("(declare-fun ")
                .append(quoteIdentifier(expr.symbol))
                .append(" (")
                .append(String.join(" ", argSorts))
                .append(") ")
                .append(printSort(LeanSmtFormulaCreator.fromFormulaType(expr.type)))
                .append(")");
            functionDecls.add(decl.toString());
          } else {
            for (Long arg : expr.arguments) {
              work.add(arg);
            }
          }
          break;
        case CONSTANT:
          break;
        default:
          throw new AssertionError("Unexpected expression kind " + expr.kind);
      }
    }
  }

  private String serialize(long handle, Map<Long, String> substitutions) {
    String replacement = substitutions.get(handle);
    if (replacement != null) {
      return replacement;
    }

    LeanSmtFormulaCreator.Expr expr = creator.getExpression(handle);
    switch (expr.kind) {
      case VARIABLE:
        return quoteIdentifier(expr.symbol);
      case CONSTANT:
        return constantToSmt(expr);
      case APPLICATION:
        String printedOp =
            expr.declarationKind == org.sosy_lab.java_smt.api.FunctionDeclarationKind.UF
                ? quoteIdentifier(expr.symbol)
                : expr.symbol;
        List<String> args = new ArrayList<>(expr.arguments.size());
        for (Long arg : expr.arguments) {
          args.add(serialize(arg, substitutions));
        }
        return "(" + printedOp + (args.isEmpty() ? "" : " " + String.join(" ", args)) + ")";
      default:
        throw new AssertionError("Unexpected expression kind " + expr.kind);
    }
  }

  private static String constantToSmt(LeanSmtFormulaCreator.Expr expr) {
    Object value = expr.constantValue;
    if (expr.type.isBitvectorType()) {
      int width = ((org.sosy_lab.java_smt.api.FormulaType.BitvectorType) expr.type).getSize();
      java.math.BigInteger unsigned = (java.math.BigInteger) value;
      String bits = unsigned.toString(2);
      if (bits.length() < width) {
        bits = "0".repeat(width - bits.length()) + bits;
      }
      return "#b" + bits;
    }
    if (value instanceof Boolean) {
      return ((Boolean) value) ? "true" : "false";
    }
    if (value instanceof java.math.BigInteger) {
      java.math.BigInteger integerValue = (java.math.BigInteger) value;
      if (integerValue.signum() < 0) {
        return "(- " + integerValue.abs() + ")";
      }
      return integerValue.toString();
    }
    if (value instanceof org.sosy_lab.common.rationals.Rational) {
      org.sosy_lab.common.rationals.Rational rationalValue =
          (org.sosy_lab.common.rationals.Rational) value;
      java.math.BigInteger numerator = rationalValue.getNum();
      java.math.BigInteger denominator = rationalValue.getDen();
      String fraction = "(/ " + numerator.abs() + " " + denominator + ")";
      if (numerator.signum() < 0) {
        return "(- " + fraction + ")";
      }
      return fraction;
    }
    return value.toString();
  }

  private static String printSort(LeanSmtType type) {
    if (type.isBool()) {
      return "Bool";
    }
    if (type.isInt()) {
      return "Int";
    }
    if (type.isReal()) {
      return "Real";
    }
    if (type.isBitvector()) {
      return "(_ BitVec " + type.getBitvectorSize() + ")";
    }
    throw new AssertionError("Unexpected sort " + type);
  }

  private static String quoteIdentifier(String id) {
    return LeanSmtFormulaCreator.encodeIdentifier(id);
  }
}
