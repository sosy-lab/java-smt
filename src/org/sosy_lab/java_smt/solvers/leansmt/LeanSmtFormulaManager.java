// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

final class LeanSmtFormulaManager
    extends AbstractFormulaManager<Long, LeanSmtType, Long, LeanSmtFunctionDecl> {

  LeanSmtFormulaManager(
      LeanSmtFormulaCreator pFormulaCreator,
      LeanSmtUFManager pFunctionManager,
      LeanSmtBooleanFormulaManager pBooleanManager,
      LeanSmtIntegerFormulaManager pIntegerManager,
      LeanSmtRationalFormulaManager pRationalManager,
      LeanSmtBitvectorFormulaManager pBitvectorManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitvectorManager,
        null,
        null,
        null,
        null,
        null,
        null);
  }

  private LeanSmtFormulaCreator creator() {
    return (LeanSmtFormulaCreator) getFormulaCreator();
  }

  @Override
  protected Long equalImpl(Long pArg1, Long pArg2) {
    return creator()
        .makeBinary(
            "=",
            org.sosy_lab.java_smt.api.FunctionDeclarationKind.EQ,
            FormulaType.BooleanType,
            pArg1,
            pArg2,
            LeanSmtNativeApi::mkEq);
  }

  @Override
  protected Long distinctImpl(Collection<Long> pArgs) {
    if (pArgs.size() < 2) {
      return creator().getTrueHandle();
    }
    List<Long> args = new ArrayList<>(pArgs);
    Long result = null;
    for (int i = 0; i < args.size(); i++) {
      for (int j = i + 1; j < args.size(); j++) {
        Long neq =
            creator()
                .makeBinary(
                    "distinct",
                    org.sosy_lab.java_smt.api.FunctionDeclarationKind.DISTINCT,
                    FormulaType.BooleanType,
                    args.get(i),
                    args.get(j),
                    LeanSmtNativeApi::mkDistinct);
        if (result == null) {
          result = neq;
        } else {
          result =
              creator()
                  .makeBinary(
                      "and",
                      org.sosy_lab.java_smt.api.FunctionDeclarationKind.AND,
                      FormulaType.BooleanType,
                      result,
                      neq,
                      LeanSmtNativeApi::mkAnd);
        }
      }
    }
    return result == null ? creator().getTrueHandle() : result;
  }

  @Override
  public Long parseImpl(String pS) throws IllegalArgumentException {
    return new LeanSmtParser(creator()).parse(pS);
  }

  @Override
  public String dumpFormulaImpl(Long pFormula) throws IOException {
    LeanSmtFormulaCreator creator = creator();

    Map<String, LeanSmtType> variableDecls = new LinkedHashMap<>();
    Set<String> functionDecls = new LinkedHashSet<>();
    collectDeclarations(pFormula, variableDecls, functionDecls);

    StringBuilder out = new StringBuilder();
    for (Map.Entry<String, LeanSmtType> v : variableDecls.entrySet()) {
      out.append("(declare-fun ")
          .append(quoteIdentifier(v.getKey()))
          .append(" () ")
          .append(printSort(v.getValue()))
          .append(")\n");
    }
    for (String decl : functionDecls) {
      out.append(decl).append('\n');
    }
    String body = serializeWithLets(pFormula, creator);
    out.append("(assert ").append(body).append(')');
    return out.toString();
  }

  private String serializeWithLets(long root, LeanSmtFormulaCreator creator) {
    Map<Long, Integer> counts = new LinkedHashMap<>();
    countOccurrences(root, creator, counts);

    List<Long> candidates = new ArrayList<>();
    collectOrder(root, creator, counts, candidates, new LinkedHashSet<>());
    if (candidates.isEmpty()) {
      return serialize(root, creator, Map.of());
    }

    Map<Long, String> substitutions = new LinkedHashMap<>();
    int idx = 0;
    for (Long c : candidates) {
      String name = "$cse" + idx++;
      substitutions.put(c, name);
    }

    String body = serialize(root, creator, substitutions);
    for (int i = candidates.size() - 1; i >= 0; i--) {
      long h = candidates.get(i);
      String name = substitutions.get(h);

      Map<Long, String> rhsSubs = new LinkedHashMap<>();
      for (int j = 0; j < i; j++) {
        long dep = candidates.get(j);
        rhsSubs.put(dep, substitutions.get(dep));
      }
      String rhs = serialize(h, creator, rhsSubs);
      body = "(let ((" + name + " " + rhs + ")) " + body + ")";
    }
    return body;
  }

  private void countOccurrences(long handle, LeanSmtFormulaCreator creator, Map<Long, Integer> counts) {
    counts.put(handle, counts.getOrDefault(handle, 0) + 1);
    LeanSmtFormulaCreator.Expr expr = creator.getExpression(handle);
    if (expr.kind == LeanSmtFormulaCreator.ExprKind.APPLICATION) {
      for (Long arg : expr.arguments) {
        countOccurrences(arg, creator, counts);
      }
    }
  }

  private void collectOrder(
      long handle,
      LeanSmtFormulaCreator creator,
      Map<Long, Integer> counts,
      List<Long> out,
      Set<Long> seen) {
    if (!seen.add(handle)) {
      return;
    }
    LeanSmtFormulaCreator.Expr expr = creator.getExpression(handle);
    if (expr.kind == LeanSmtFormulaCreator.ExprKind.APPLICATION) {
      for (Long arg : expr.arguments) {
        collectOrder(arg, creator, counts, out, seen);
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
    LeanSmtFormulaCreator creator = creator();

    while (!work.isEmpty()) {
      long h = work.removeLast();
      if (!seen.add(h)) {
        continue;
      }
      LeanSmtFormulaCreator.Expr expr = creator.getExpression(h);
      switch (expr.kind) {
        case VARIABLE:
          variableDecls.putIfAbsent(expr.symbol, LeanSmtFormulaCreator.fromFormulaType(expr.type));
          break;
        case APPLICATION:
          if (expr.declarationKind == org.sosy_lab.java_smt.api.FunctionDeclarationKind.UF) {
            List<String> argSorts = new ArrayList<>(expr.arguments.size());
            for (Long arg : expr.arguments) {
              FormulaType<?> t = creator.getFormulaType(arg);
              argSorts.add(printSort(LeanSmtFormulaCreator.fromFormulaType(t)));
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
          break;
      }
    }
  }

  private String serialize(long handle, LeanSmtFormulaCreator creator, Map<Long, String> substitutions) {
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
        String op = expr.symbol;
        String printedOp =
            "=>".equals(op)
                ? "=>"
                : (op.startsWith("(_ ") && op.endsWith(")")) ? op : quoteIdentifier(op);
        List<String> args = new ArrayList<>(expr.arguments.size());
        for (Long arg : expr.arguments) {
          args.add(serialize(arg, creator, substitutions));
        }
        return "(" + printedOp + (args.isEmpty() ? "" : " " + String.join(" ", args)) + ")";
      default:
        throw new AssertionError("Unexpected expression kind " + expr.kind);
    }
  }

  private static String constantToSmt(LeanSmtFormulaCreator.Expr expr) {
    Object value = expr.constantValue;
    if (expr.type.isBitvectorType()) {
      int width = ((FormulaType.BitvectorType) expr.type).getSize();
      BigInteger unsigned = (BigInteger) value;
      String bits = unsigned.toString(2);
      if (bits.length() < width) {
        bits = "0".repeat(width - bits.length()) + bits;
      }
      return "#b" + bits;
    }
    if (value instanceof Boolean) {
      return ((Boolean) value) ? "true" : "false";
    }
    if (value instanceof BigInteger) {
      BigInteger v = (BigInteger) value;
      if (v.signum() < 0) {
        return "(- " + v.abs() + ")";
      }
      return v.toString();
    }
    if (value instanceof org.sosy_lab.common.rationals.Rational) {
      org.sosy_lab.common.rationals.Rational r = (org.sosy_lab.common.rationals.Rational) value;
      BigInteger n = r.getNum();
      BigInteger d = r.getDen();
      if (d.equals(BigInteger.ONE)) {
        if (n.signum() < 0) {
          return "(- " + n.abs() + ")";
        }
        return n.toString();
      }
      String frac = "(/ " + n.abs() + " " + d + ")";
      if (n.signum() < 0) {
        return "(- " + frac + ")";
      }
      return frac;
    }
    return value.toString();
  }

  private static String printSort(LeanSmtType t) {
    if (t.isBool()) {
      return "Bool";
    }
    if (t.isInt()) {
      return "Int";
    }
    if (t.isReal()) {
      return "Real";
    }
    if (t.isBitvector()) {
      return "(_ BitVec " + t.getBitvectorSize() + ")";
    }
    throw new AssertionError("Unexpected sort " + t);
  }

  private static String quoteIdentifier(String id) {
    if (id.matches("[a-zA-Z~!@$%^&*_+=<>.?/-][a-zA-Z0-9~!@$%^&*_+=<>.?/-]*")
        && !id.startsWith(":")) {
      return id;
    }
    return "|" + id.replace("|", "||") + "|";
  }
}
