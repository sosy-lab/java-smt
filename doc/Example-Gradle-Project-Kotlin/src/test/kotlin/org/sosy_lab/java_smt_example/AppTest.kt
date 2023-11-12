// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt_example;

import kotlin.test.Test

class AppTest {

  @Test
  fun z3SudokuTest() {
    SudokuTest().z3SudokuTest()
  }

  @Test
  fun princessSudokuTest() {
    SudokuTest().princessSudokuTest()
  }

  @Test
  fun smtInterpolSudokuTest() {
    SudokuTest().smtInterpolSudokuTest()
  }

  @Test
  fun cvc4SudokuTest() {
    SudokuTest().cvc4SudokuTest()
  }

  @Test
  fun mathsatSudokuTest() {
    SudokuTest().mathsatSudokuTest()
  }

  @Test
  fun boolectorSudokuTest() {
    SudokuTest().boolectorSudokuTest()
  }

  @Test
  fun yicesSudokuTest() {
    SudokuTest().yicesSudokuTest()
  }
}