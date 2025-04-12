// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.utils;

import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

public final class PrettyPrinter {

  public enum PrinterOption {
    /** introduce newlines only for boolean operations, instead of for all operations. */
    SPLIT_ONLY_BOOLEAN_OPERATIONS
  }

  private final FormulaManager fmgr;

  public PrettyPrinter(FormulaManager pFmgr) {
    fmgr = pFmgr;
  }

  /**
   * This method returns a multi-line String with pretty-formatted and indented subformulas.
   *
   * <p>The String representation might contain solver-specific symbols that appear during a
   * visitation of the formula. The returned String is intended to be human-readable and should not
   * be used for further processing. The formatting of this string might change with future
   * development and thus is not considered as "stable". If a user wants to apply further
   * processing, we refer to {@link FormulaManager#dumpFormula} that provides machine-readable
   * SMTLIB2.
   */
  public String formulaToString(Formula f, PrinterOption... options) {
    StringBuilder str = new StringBuilder();
    fmgr.visit(f, new PrettyPrintVisitor(fmgr, str, ImmutableSet.copyOf(options)));
    return str.toString();
  }

  /**
   * This method returns a Graphviz/Dot representation of the given formula.
   *
   * <p>The graph representation might contain solver-specific symbols that appear during a
   * visitation of the formula. The returned String is intended to be a human-readable graph for
   * Graphviz/Dot and should not be used for further processing. The formatting of this string might
   * change with future development and thus is not considered as "stable". If a user wants to apply
   * further processing, we refer to {@link FormulaManager#dumpFormula} that provides
   * machine-readable SMTLIB2.
   */
  public String formulaToDot(Formula f, PrinterOption... options) {
    DotVisitor plotter = new DotVisitor(ImmutableSet.copyOf(options));
    fmgr.visitRecursively(f, plotter);
    return plotter.toString();
  }

  private static boolean isBooleanFunction(FunctionDeclarationKind kind) {
    switch (kind) {
      case AND:
      case OR:
      case NOT:
      case ITE:
      case IFF:
      case XOR:
      case IMPLIES:
        return true;
      default:
        return false;
    }
  }

  private static String getColor(FunctionDeclarationKind kind) {
    switch (kind) {
      case AND:
        return "lightblue";
      case OR:
        return "lightgreen";
      case NOT:
        return "orange";
      case ITE:
        return "yellow";
      case IFF:
      case XOR:
      case IMPLIES:
        return "lightpink";
      default:
        return "white";
    }
  }

  private static String getEdgeLabel(FunctionDeclarationKind kind, int operandId) {
    // for some functions, the order of operands is not important, so we return an empty String
    switch (kind) {
      case AND:
      case OR:
      case NOT:
      case IFF:
      case XOR:
        return "";
      default:
        return Integer.toString(operandId);
    }
  }

  private static final class PrettyPrintVisitor extends DefaultFormulaVisitor<Void> {

    private final FormulaManager fmgr;
    private final StringBuilder out;
    private final boolean onlyBooleanOperations;
    private int depth = 0;

    /** flag to enable or disable splitting formulas in multiple lines. */
    private boolean enableSplitting = true;

    private PrettyPrintVisitor(
        FormulaManager pFmgr, StringBuilder pStr, Collection<PrinterOption> pOptions) {
      fmgr = pFmgr;
      out = pStr;
      onlyBooleanOperations = pOptions.contains(PrinterOption.SPLIT_ONLY_BOOLEAN_OPERATIONS);
    }

    /** add a newline and space for indent if required, and a simple whitespace otherwise. */
    private void newline() {
      if (enableSplitting) {
        if (out.length() != 0) {
          out.append(System.lineSeparator());
        }
        out.append("  ".repeat(depth)); // two spaces indent is sufficient
      } else {
        out.append(" "); // just a separator between two tokens
      }
    }

    @Override
    protected Void visitDefault(Formula pF) {
      newline();
      out.append(pF);
      return null;
    }

    @Override
    public Void visitFunction(
        Formula pF, List<Formula> pArgs, FunctionDeclaration<?> pFunctionDeclaration) {
      newline();
      out.append("(").append(pFunctionDeclaration.getName());

      boolean splitNested = true;
      // we only change the flag
      // - if splitting is still allowed (recursive formulas!) and
      // - if we should not split INT or BV arithmetics
      if (enableSplitting
          && onlyBooleanOperations
          && !isBooleanFunction(pFunctionDeclaration.getKind())) {
        splitNested = false;
      }
      if (!splitNested) { // disable deeper splitting
        enableSplitting = false;
      }

      depth++;
      for (Formula arg : pArgs) {
        fmgr.visit(arg, this);
      }
      depth--;

      if (enableSplitting) { // avoid superflous whitespace before closing bracket
        newline();
      }

      out.append(")");
      if (!splitNested) { // reset flag
        enableSplitting = true;
      }
      return null;
    }
  }

  private static final class DotVisitor extends DefaultFormulaVisitor<TraversalProcess> {

    private final Map<Formula, Integer> nodeMapping = new LinkedHashMap<>();
    private final UniqueIdGenerator id = new UniqueIdGenerator();
    private final boolean onlyBooleanOperations;

    // start of dot-file, rest will be appended on visitation
    private final StringBuilder out =
        new StringBuilder(
            "digraph SMT {" + System.lineSeparator() + "  rankdir=LR" + System.lineSeparator());

    // let's print leave-nodes lazily, having them on same rank looks nicer in the plot.
    private final List<String> leaves = new ArrayList<>();

    private DotVisitor(Collection<PrinterOption> pOptions) {
      onlyBooleanOperations = pOptions.contains(PrinterOption.SPLIT_ONLY_BOOLEAN_OPERATIONS);
    }

    @Override
    public String toString() {

      // let's put non-expanded leaf-nodes onto the right side
      if (!leaves.isEmpty()) {
        out.append("  { rank=same;").append(System.lineSeparator());
        leaves.forEach(out::append);
        out.append("  }").append(System.lineSeparator());
      }

      // end of dot-file
      out.append("}");
      return out.toString();
    }

    private int getId(Formula f) {
      return nodeMapping.computeIfAbsent(f, unused -> id.getFreshId());
    }

    private String formatNode(Formula f, String label) {
      return formatNode(f, label, "rectangle", "white");
    }

    private String formatNode(Formula f, String label, String shape, String color) {
      return String.format(
          "  %d [label=\"%s\", shape=\"%s\", style=\"filled\", fillcolor=\"%s\"];%n",
          getId(f), label, shape, color);
    }

    private String formatEdge(Formula from, Formula to, String label) {
      return String.format("  %d -> %d [label=\"%s\"];%n", getId(from), getId(to), label);
    }

    @Override
    protected TraversalProcess visitDefault(Formula pF) {
      out.append(formatNode(pF, pF.toString()));
      return TraversalProcess.CONTINUE;
    }

    @Override
    public TraversalProcess visitConstant(Formula pF, Object value) {
      out.append(formatNode(pF, pF.toString(), "rectangle", "grey"));
      return TraversalProcess.CONTINUE;
    }

    @Override
    public TraversalProcess visitFunction(
        Formula pF, List<Formula> pArgs, FunctionDeclaration<?> pFunctionDeclaration) {
      FunctionDeclarationKind kind = pFunctionDeclaration.getKind();
      // we skip subformulas
      // - if splitting is still allowed (recursive formulas!) and
      // - if we should not split INT or BV arithmetics
      if (onlyBooleanOperations && !isBooleanFunction(kind)) {
        // for leaves, we just dump the formula. This might include redundant subformulas.
        leaves.add("  " + formatNode(pF, pF.toString()));
        return TraversalProcess.SKIP;
      } else {
        String color = getColor(kind);
        // we expect small labels, so circle-shape is sufficiently small
        out.append(formatNode(pF, pFunctionDeclaration.getName(), "circle", color));
        int operandId = 0;
        for (Formula arg : pArgs) {
          out.append(formatEdge(pF, arg, getEdgeLabel(kind, operandId++)));
        }
        return TraversalProcess.CONTINUE;
      }
    }
  }
}
