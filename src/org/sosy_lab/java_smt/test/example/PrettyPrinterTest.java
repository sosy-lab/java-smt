/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test.example;

import static com.google.common.truth.Truth.assertThat;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.sosy_lab.java_smt.test.SolverBasedTest0.ParameterizedSolverBasedTest0;
import org.sosy_lab.java_smt.utils.PrettyPrinter;
import org.sosy_lab.java_smt.utils.PrettyPrinter.PrinterOption;

public class PrettyPrinterTest extends ParameterizedSolverBasedTest0 {

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

  @BeforeEach
  public void init() {
    pp = new PrettyPrinter(context.getFormulaManager());
  }

  @Test
  public void testPrettyPrintOnlyBoolean() {
    requireParser();
    requireIntegers();
    requireRationals();
    requireArrays();

    String expected =
        switch (solverToUse()) {
          case MATHSAT5 ->
              """
              (`and`
                (`=_int` (`read_int_int` arr x) (foo 3))
                (`not`
                  (`<=_int` xx x)
                )
              )\
              """;
          case PRINCESS ->
              """
              (And
                (= (select arr x) (foo 3))
                (GeqZero (+ (+ xx (* -1 x)) -1))
              )\
              """;
          case OPENSMT ->
              """
              (and
                (= (select arr x) (foo 3))
                (not
                  (<= 0 (+ x (* -1 xx)))
                )
              )\
              """;
          default ->
              """
              (and
                (= (select arr x) (foo 3))
                (< x xx)
              )\
              """;
        };
    expected = expected.replace("\n", System.lineSeparator());
    assertThat(
            pp.formulaToString(
                mgr.parse(VARS + QUERY_1), PrinterOption.SPLIT_ONLY_BOOLEAN_OPERATIONS))
        .isEqualTo(expected);
  }

  @Test
  public void testPrettyPrintAll() {
    requireParser();
    requireIntegers();
    requireRationals();
    requireArrays();

    String expected =
        switch (solverToUse()) {
          case MATHSAT5 ->
              """
              (`and`
                (`=_int`
                  (`read_int_int`
                    arr
                    x
                  )
                  (foo
                    3
                  )
                )
                (`not`
                  (`<=_int`
                    xx
                    x
                  )
                )
              )\
              """;
          case PRINCESS ->
              """
              (And
                (=
                  (select
                    arr
                    x
                  )
                  (foo
                    3
                  )
                )
                (GeqZero
                  (+
                    (+
                      xx
                      (*
                        -1
                        x
                      )
                    )
                    -1
                  )
                )
              )\
              """;
          case OPENSMT ->
              """
              (and
                (=
                  (select
                    arr
                    x
                  )
                  (foo
                    3
                  )
                )
                (not
                  (<=
                    0
                    (+
                      x
                      (*
                        -1
                        xx
                      )
                    )
                  )
                )
              )\
              """;
          default ->
              """
              (and
                (=
                  (select
                    arr
                    x
                  )
                  (foo
                    3
                  )
                )
                (<
                  x
                  xx
                )
              )\
              """;
        };
    expected = expected.replace("\n", System.lineSeparator());
    assertThat(pp.formulaToString(mgr.parse(VARS + QUERY_1))).isEqualTo(expected);
  }

  @SuppressWarnings("checkstyle:LineLength")
  @Test
  public void testDotOnlyBoolean() {
    requireParser();
    requireIntegers();
    requireRationals();
    requireArrays();

    String expected =
        switch (solverToUse()) {
          case MATHSAT5 ->
              """
              digraph SMT {
                rankdir=LR
                0 [label="`and`", shape="circle", style="filled", fillcolor="lightblue"];
                0 -> 1 [label=""];
                0 -> 2 [label=""];
                2 [label="`not`", shape="circle", style="filled", fillcolor="orange"];
                2 -> 3 [label=""];
                { rank=same;
                  3 [label="(`<=_int` xx x)", shape="rectangle", style="filled", fillcolor="white"];
                  1 [label="(`=_int` (`read_int_int` arr x) (foo 3))", shape="rectangle", style="filled", fillcolor="white"];
                }
              }\
              """;
          case PRINCESS ->
              """
              digraph SMT {
                rankdir=LR
                0 [label="And", shape="circle", style="filled", fillcolor="lightblue"];
                0 -> 1 [label=""];
                0 -> 2 [label=""];
                { rank=same;
                  2 [label="(((xx + -1 * x) + -1) >= 0)", shape="rectangle", style="filled", fillcolor="white"];
                  1 [label="(select(arr, x) = foo(3))", shape="rectangle", style="filled", fillcolor="white"];
                }
              }\
              """;
          case OPENSMT ->
              """
              digraph SMT {
                rankdir=LR
                0 [label="and", shape="circle", style="filled", fillcolor="lightblue"];
                0 -> 1 [label=""];
                0 -> 2 [label=""];
                2 [label="not", shape="circle", style="filled", fillcolor="orange"];
                2 -> 3 [label=""];
                { rank=same;
                  3 [label="(<= 0 (+ x (* -1 xx)))", shape="rectangle", style="filled", fillcolor="white"];
                  1 [label="(= (select arr x) (foo 3))", shape="rectangle", style="filled", fillcolor="white"];
                }
              }\
              """;
          default ->
              """
              digraph SMT {
                rankdir=LR
                0 [label="and", shape="circle", style="filled", fillcolor="lightblue"];
                0 -> 1 [label=""];
                0 -> 2 [label=""];
                { rank=same;
                  2 [label="(< x xx)", shape="rectangle", style="filled", fillcolor="white"];
                  1 [label="(= (select arr x) (foo 3))", shape="rectangle", style="filled", fillcolor="white"];
                }
              }\
              """;
        };
    expected = expected.replace("\n", System.lineSeparator());
    assertThat(
            pp.formulaToDot(mgr.parse(VARS + QUERY_1), PrinterOption.SPLIT_ONLY_BOOLEAN_OPERATIONS))
        .isEqualTo(expected);
  }

  @Test
  public void testDotAll() {
    requireParser();
    requireIntegers();
    requireRationals();
    requireArrays();

    String expected =
        switch (solverToUse()) {
          case MATHSAT5 ->
              """
              digraph SMT {
                rankdir=LR
                0 [label="`and`", shape="circle", style="filled", fillcolor="lightblue"];
                0 -> 1 [label=""];
                0 -> 2 [label=""];
                2 [label="`not`", shape="circle", style="filled", fillcolor="orange"];
                2 -> 3 [label=""];
                3 [label="`<=_int`", shape="circle", style="filled", fillcolor="white"];
                3 -> 4 [label="0"];
                3 -> 5 [label="1"];
                5 [label="x", shape="rectangle", style="filled", fillcolor="white"];
                4 [label="xx", shape="rectangle", style="filled", fillcolor="white"];
                1 [label="`=_int`", shape="circle", style="filled", fillcolor="white"];
                1 -> 6 [label="0"];
                1 -> 7 [label="1"];
                7 [label="foo", shape="circle", style="filled", fillcolor="white"];
                7 -> 8 [label="0"];
                8 [label="3", shape="rectangle", style="filled", fillcolor="grey"];
                6 [label="`read_int_int`", shape="circle", style="filled", fillcolor="white"];
                6 -> 9 [label="0"];
                6 -> 5 [label="1"];
                9 [label="arr", shape="rectangle", style="filled", fillcolor="white"];
              }\
              """;
          case PRINCESS ->
              """
              digraph SMT {
                rankdir=LR
                0 [label="And", shape="circle", style="filled", fillcolor="lightblue"];
                0 -> 1 [label=""];
                0 -> 2 [label=""];
                2 [label="GeqZero", shape="circle", style="filled", fillcolor="white"];
                2 -> 3 [label="0"];
                3 [label="+", shape="circle", style="filled", fillcolor="white"];
                3 -> 4 [label="0"];
                3 -> 5 [label="1"];
                5 [label="-1", shape="rectangle", style="filled", fillcolor="grey"];
                4 [label="+", shape="circle", style="filled", fillcolor="white"];
                4 -> 6 [label="0"];
                4 -> 7 [label="1"];
                7 [label="*", shape="circle", style="filled", fillcolor="white"];
                7 -> 5 [label="0"];
                7 -> 8 [label="1"];
                8 [label="x", shape="rectangle", style="filled", fillcolor="white"];
                6 [label="xx", shape="rectangle", style="filled", fillcolor="white"];
                1 [label="=", shape="circle", style="filled", fillcolor="white"];
                1 -> 9 [label="0"];
                1 -> 10 [label="1"];
                10 [label="foo", shape="circle", style="filled", fillcolor="white"];
                10 -> 11 [label="0"];
                11 [label="3", shape="rectangle", style="filled", fillcolor="grey"];
                9 [label="select", shape="circle", style="filled", fillcolor="white"];
                9 -> 12 [label="0"];
                9 -> 8 [label="1"];
                12 [label="arr", shape="rectangle", style="filled", fillcolor="white"];
              }\
              """;
          case OPENSMT ->
              """
              digraph SMT {
                rankdir=LR
                0 [label="and", shape="circle", style="filled", fillcolor="lightblue"];
                0 -> 1 [label=""];
                0 -> 2 [label=""];
                2 [label="not", shape="circle", style="filled", fillcolor="orange"];
                2 -> 3 [label=""];
                3 [label="<=", shape="circle", style="filled", fillcolor="white"];
                3 -> 4 [label="0"];
                3 -> 5 [label="1"];
                5 [label="+", shape="circle", style="filled", fillcolor="white"];
                5 -> 6 [label="0"];
                5 -> 7 [label="1"];
                7 [label="*", shape="circle", style="filled", fillcolor="white"];
                7 -> 8 [label="0"];
                7 -> 9 [label="1"];
                9 [label="xx", shape="rectangle", style="filled", fillcolor="white"];
                8 [label="-1", shape="rectangle", style="filled", fillcolor="grey"];
                6 [label="x", shape="rectangle", style="filled", fillcolor="white"];
                4 [label="0", shape="rectangle", style="filled", fillcolor="grey"];
                1 [label="=", shape="circle", style="filled", fillcolor="white"];
                1 -> 10 [label="0"];
                1 -> 11 [label="1"];
                11 [label="foo", shape="circle", style="filled", fillcolor="white"];
                11 -> 12 [label="0"];
                12 [label="3", shape="rectangle", style="filled", fillcolor="grey"];
                10 [label="select", shape="circle", style="filled", fillcolor="white"];
                10 -> 13 [label="0"];
                10 -> 6 [label="1"];
                13 [label="arr", shape="rectangle", style="filled", fillcolor="white"];
              }\
              """;
          default ->
              """
              digraph SMT {
                rankdir=LR
                0 [label="and", shape="circle", style="filled", fillcolor="lightblue"];
                0 -> 1 [label=""];
                0 -> 2 [label=""];
                2 [label="<", shape="circle", style="filled", fillcolor="white"];
                2 -> 3 [label="0"];
                2 -> 4 [label="1"];
                4 [label="xx", shape="rectangle", style="filled", fillcolor="white"];
                3 [label="x", shape="rectangle", style="filled", fillcolor="white"];
                1 [label="=", shape="circle", style="filled", fillcolor="white"];
                1 -> 5 [label="0"];
                1 -> 6 [label="1"];
                6 [label="foo", shape="circle", style="filled", fillcolor="white"];
                6 -> 7 [label="0"];
                7 [label="3", shape="rectangle", style="filled", fillcolor="grey"];
                5 [label="select", shape="circle", style="filled", fillcolor="white"];
                5 -> 8 [label="0"];
                5 -> 3 [label="1"];
                8 [label="arr", shape="rectangle", style="filled", fillcolor="white"];
              }\
              """;
        };
    expected = expected.replace("\n", System.lineSeparator());
    assertThat(pp.formulaToDot(mgr.parse(VARS + QUERY_1))).isEqualTo(expected);
  }
}
