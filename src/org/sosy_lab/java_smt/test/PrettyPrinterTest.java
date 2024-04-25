// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.utils.PrettyPrinter;
import org.sosy_lab.java_smt.utils.PrettyPrinter.PrinterOption;

public class PrettyPrinterTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  private PrettyPrinter pp;

  private static final String VARS =
      "(declare-fun x () Int)"
          + "(declare-fun xx () Int)"
          + "(declare-fun y () Real)"
          + "(declare-fun yy () Real)"
          + "(declare-fun arr () (Array Int Int))"
          + "(declare-fun arr2 () (Array Int Int))"
          + "(declare-fun foo (Int) Int)"
          + "(declare-fun bar (Real) Real)";

  private static final String QUERY_1 = "(assert (and (= (select arr x) (foo 3)) (< x xx)))";

  @Before
  public void init() {
    pp = new PrettyPrinter(context.getFormulaManager());
  }

  @Test
  public void testPrettyPrintOnlyBoolean() {
    requireParser();
    String expected;
    switch (solverToUse()) {
      case MATHSAT5:
        expected =
            "(`and`\n"
                + "  (`=_int` (`read_int_int` arr x) (foo 3))\n"
                + "  (`not`\n"
                + "    (`<=_int` xx x)\n"
                + "  )\n"
                + ")";
        break;
      case PRINCESS:
        expected =
            "(And\n"
                + "  (= (select arr x) (foo 3))\n"
                + "  (GeqZero (+ (+ xx (* -1 x)) -1))\n"
                + ")";
        break;
      case OPENSMT:
        expected =
            "(and\n"
                + "  (= (select arr x) (foo 3))\n"
                + "  (not\n"
                + "    (<= 0 (+ x (* -1 xx)))\n"
                + "  )\n"
                + ")";
        break;
      default:
        expected = "(and\n" + "  (= (select arr x) (foo 3))\n" + "  (< x xx)\n" + ")";
    }
    expected = expected.replace("\n", System.lineSeparator());
    assertThat(
            pp.formulaToString(
                mgr.parse(VARS + QUERY_1), PrinterOption.SPLIT_ONLY_BOOLEAN_OPERATIONS))
        .isEqualTo(expected);
  }

  @Test
  public void testPrettyPrintAll() {
    requireParser();
    String expected;
    switch (solverToUse()) {
      case MATHSAT5:
        expected =
            "(`and`\n"
                + "  (`=_int`\n"
                + "    (`read_int_int`\n"
                + "      arr\n"
                + "      x\n"
                + "    )\n"
                + "    (foo\n"
                + "      3\n"
                + "    )\n"
                + "  )\n"
                + "  (`not`\n"
                + "    (`<=_int`\n"
                + "      xx\n"
                + "      x\n"
                + "    )\n"
                + "  )\n"
                + ")";
        break;
      case PRINCESS:
        expected =
            "(And\n"
                + "  (=\n"
                + "    (select\n"
                + "      arr\n"
                + "      x\n"
                + "    )\n"
                + "    (foo\n"
                + "      3\n"
                + "    )\n"
                + "  )\n"
                + "  (GeqZero\n"
                + "    (+\n"
                + "      (+\n"
                + "        xx\n"
                + "        (*\n"
                + "          -1\n"
                + "          x\n"
                + "        )\n"
                + "      )\n"
                + "      -1\n"
                + "    )\n"
                + "  )\n"
                + ")";
        break;
      case OPENSMT:
        expected =
            "(and\n"
                + "  (=\n"
                + "    (select\n"
                + "      arr\n"
                + "      x\n"
                + "    )\n"
                + "    (foo\n"
                + "      3\n"
                + "    )\n"
                + "  )\n"
                + "  (not\n"
                + "    (<=\n"
                + "      0\n"
                + "      (+\n"
                + "        x\n"
                + "        (*\n"
                + "          -1\n"
                + "          xx\n"
                + "        )\n"
                + "      )\n"
                + "    )\n"
                + "  )\n"
                + ")";
        break;
      default:
        expected =
            "(and\n"
                + "  (=\n"
                + "    (select\n"
                + "      arr\n"
                + "      x\n"
                + "    )\n"
                + "    (foo\n"
                + "      3\n"
                + "    )\n"
                + "  )\n"
                + "  (<\n"
                + "    x\n"
                + "    xx\n"
                + "  )\n"
                + ")";
    }
    expected = expected.replace("\n", System.lineSeparator());
    assertThat(pp.formulaToString(mgr.parse(VARS + QUERY_1))).isEqualTo(expected);
  }

  @Test
  public void testDotOnlyBoolean() {
    requireParser();
    String expected;
    switch (solverToUse()) {
      case MATHSAT5:
        expected =
            "digraph SMT {\n"
                + "  rankdir=LR\n"
                + "  0 [label=\"`and`\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"lightblue\"];\n"
                + "  0 -> 1 [label=\"\"];\n"
                + "  0 -> 2 [label=\"\"];\n"
                + "  2 [label=\"`not`\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"orange\"];\n"
                + "  2 -> 3 [label=\"\"];\n"
                + "  { rank=same;\n"
                + "    3 [label=\"(`<=_int` xx x)\", shape=\"rectangle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "    1 [label=\"(`=_int` (`read_int_int` arr x) (foo 3))\", shape=\"rectangle\","
                + " style=\"filled\", fillcolor=\"white\"];\n"
                + "  }\n"
                + "}";
        break;
      case PRINCESS:
        expected =
            "digraph SMT {\n"
                + "  rankdir=LR\n"
                + "  0 [label=\"And\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"lightblue\"];\n"
                + "  0 -> 1 [label=\"\"];\n"
                + "  0 -> 2 [label=\"\"];\n"
                + "  { rank=same;\n"
                + "    2 [label=\"(((xx + -1 * x) + -1) >= 0)\", shape=\"rectangle\","
                + " style=\"filled\", fillcolor=\"white\"];\n"
                + "    1 [label=\"(select(arr, x) = foo(3))\", shape=\"rectangle\","
                + " style=\"filled\", fillcolor=\"white\"];\n"
                + "  }\n"
                + "}";
        break;
      case OPENSMT:
        expected =
            "digraph SMT {\n"
                + "  rankdir=LR\n"
                + "  0 [label=\"and\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"lightblue\"];\n"
                + "  0 -> 1 [label=\"\"];\n"
                + "  0 -> 2 [label=\"\"];\n"
                + "  2 [label=\"not\", shape=\"circle\", style=\"filled\", fillcolor=\"orange\"];\n"
                + "  2 -> 3 [label=\"\"];\n"
                + "  { rank=same;\n"
                + "    3 [label=\"(<= 0 (+ x (* -1 xx)))\", shape=\"rectangle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "    1 [label=\"(= (select arr x) (foo 3))\", shape=\"rectangle\","
                + " style=\"filled\", fillcolor=\"white\"];\n"
                + "  }\n"
                + "}";
        break;
      default:
        expected =
            "digraph SMT {\n"
                + "  rankdir=LR\n"
                + "  0 [label=\"and\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"lightblue\"];\n"
                + "  0 -> 1 [label=\"\"];\n"
                + "  0 -> 2 [label=\"\"];\n"
                + "  { rank=same;\n"
                + "    2 [label=\"(< x xx)\", shape=\"rectangle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "    1 [label=\"(= (select arr x) (foo 3))\", shape=\"rectangle\","
                + " style=\"filled\", fillcolor=\"white\"];\n"
                + "  }\n"
                + "}";
    }
    expected = expected.replace("\n", System.lineSeparator());
    assertThat(
            pp.formulaToDot(mgr.parse(VARS + QUERY_1), PrinterOption.SPLIT_ONLY_BOOLEAN_OPERATIONS))
        .isEqualTo(expected);
  }

  @Test
  public void testDotAll() {
    requireParser();
    String expected;
    switch (solverToUse()) {
      case MATHSAT5:
        expected =
            "digraph SMT {\n"
                + "  rankdir=LR\n"
                + "  0 [label=\"`and`\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"lightblue\"];\n"
                + "  0 -> 1 [label=\"\"];\n"
                + "  0 -> 2 [label=\"\"];\n"
                + "  2 [label=\"`not`\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"orange\"];\n"
                + "  2 -> 3 [label=\"\"];\n"
                + "  3 [label=\"`<=_int`\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "  3 -> 4 [label=\"0\"];\n"
                + "  3 -> 5 [label=\"1\"];\n"
                + "  5 [label=\"x\", shape=\"rectangle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  4 [label=\"xx\", shape=\"rectangle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "  1 [label=\"`=_int`\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "  1 -> 6 [label=\"0\"];\n"
                + "  1 -> 7 [label=\"1\"];\n"
                + "  7 [label=\"foo\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  7 -> 8 [label=\"0\"];\n"
                + "  8 [label=\"3\", shape=\"rectangle\", style=\"filled\", fillcolor=\"grey\"];\n"
                + "  6 [label=\"`read_int_int`\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "  6 -> 9 [label=\"0\"];\n"
                + "  6 -> 5 [label=\"1\"];\n"
                + "  9 [label=\"arr\", shape=\"rectangle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "}";
        break;
      case PRINCESS:
        expected =
            "digraph SMT {\n"
                + "  rankdir=LR\n"
                + "  0 [label=\"And\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"lightblue\"];\n"
                + "  0 -> 1 [label=\"\"];\n"
                + "  0 -> 2 [label=\"\"];\n"
                + "  2 [label=\"GeqZero\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "  2 -> 3 [label=\"0\"];\n"
                + "  3 [label=\"+\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  3 -> 4 [label=\"0\"];\n"
                + "  3 -> 5 [label=\"1\"];\n"
                + "  5 [label=\"-1\", shape=\"rectangle\", style=\"filled\", fillcolor=\"grey\"];\n"
                + "  4 [label=\"+\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  4 -> 6 [label=\"0\"];\n"
                + "  4 -> 7 [label=\"1\"];\n"
                + "  7 [label=\"*\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  7 -> 5 [label=\"0\"];\n"
                + "  7 -> 8 [label=\"1\"];\n"
                + "  8 [label=\"x\", shape=\"rectangle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  6 [label=\"xx\", shape=\"rectangle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "  1 [label=\"=\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  1 -> 9 [label=\"0\"];\n"
                + "  1 -> 10 [label=\"1\"];\n"
                + "  10 [label=\"foo\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  10 -> 11 [label=\"0\"];\n"
                + "  11 [label=\"3\", shape=\"rectangle\", style=\"filled\", fillcolor=\"grey\"];\n"
                + "  9 [label=\"select\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "  9 -> 12 [label=\"0\"];\n"
                + "  9 -> 8 [label=\"1\"];\n"
                + "  12 [label=\"arr\", shape=\"rectangle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "}";
        break;
      case OPENSMT:
        expected =
            "digraph SMT {\n"
                + "  rankdir=LR\n"
                + "  0 [label=\"and\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"lightblue\"];\n"
                + "  0 -> 1 [label=\"\"];\n"
                + "  0 -> 2 [label=\"\"];\n"
                + "  2 [label=\"not\", shape=\"circle\", style=\"filled\", fillcolor=\"orange\"];\n"
                + "  2 -> 3 [label=\"\"];\n"
                + "  3 [label=\"<=\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  3 -> 4 [label=\"0\"];\n"
                + "  3 -> 5 [label=\"1\"];\n"
                + "  5 [label=\"+\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  5 -> 6 [label=\"0\"];\n"
                + "  5 -> 7 [label=\"1\"];\n"
                + "  7 [label=\"*\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  7 -> 8 [label=\"0\"];\n"
                + "  7 -> 9 [label=\"1\"];\n"
                + "  9 [label=\"xx\", shape=\"rectangle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "  8 [label=\"-1\", shape=\"rectangle\", style=\"filled\", fillcolor=\"grey\"];\n"
                + "  6 [label=\"x\", shape=\"rectangle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  4 [label=\"0\", shape=\"rectangle\", style=\"filled\", fillcolor=\"grey\"];\n"
                + "  1 [label=\"=\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  1 -> 10 [label=\"0\"];\n"
                + "  1 -> 11 [label=\"1\"];\n"
                + "  11 [label=\"foo\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  11 -> 12 [label=\"0\"];\n"
                + "  12 [label=\"3\", shape=\"rectangle\", style=\"filled\", fillcolor=\"grey\"];\n"
                + "  10 [label=\"select\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "  10 -> 13 [label=\"0\"];\n"
                + "  10 -> 6 [label=\"1\"];\n"
                + "  13 [label=\"arr\", shape=\"rectangle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "}";
        break;
      default:
        expected =
            "digraph SMT {\n"
                + "  rankdir=LR\n"
                + "  0 [label=\"and\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"lightblue\"];\n"
                + "  0 -> 1 [label=\"\"];\n"
                + "  0 -> 2 [label=\"\"];\n"
                + "  2 [label=\"<\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  2 -> 3 [label=\"0\"];\n"
                + "  2 -> 4 [label=\"1\"];\n"
                + "  4 [label=\"xx\", shape=\"rectangle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "  3 [label=\"x\", shape=\"rectangle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  1 [label=\"=\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  1 -> 5 [label=\"0\"];\n"
                + "  1 -> 6 [label=\"1\"];\n"
                + "  6 [label=\"foo\", shape=\"circle\", style=\"filled\", fillcolor=\"white\"];\n"
                + "  6 -> 7 [label=\"0\"];\n"
                + "  7 [label=\"3\", shape=\"rectangle\", style=\"filled\", fillcolor=\"grey\"];\n"
                + "  5 [label=\"select\", shape=\"circle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "  5 -> 8 [label=\"0\"];\n"
                + "  5 -> 3 [label=\"1\"];\n"
                + "  8 [label=\"arr\", shape=\"rectangle\", style=\"filled\","
                + " fillcolor=\"white\"];\n"
                + "}";
    }
    expected = expected.replace("\n", System.lineSeparator());
    assertThat(pp.formulaToDot(mgr.parse(VARS + QUERY_1))).isEqualTo(expected);
  }
}
