// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt_example;

import org.sosy_lab.java_smt.example.SolverOverviewTable
import org.sosy_lab.java_smt.example.SolverOverviewTable.RowBuilder
import org.sosy_lab.java_smt.SolverContextFactory.Solvers
import org.sosy_lab.java_smt.example.SolverOverviewTable.SolverInfo

/*
 * Use the JavaSMT SolverOverviewTable example in Kotlin as a example application as
 * it checks/uses all available solvers.
 */
fun main() {
  val infos: MutableList<SolverInfo> = mutableListOf()
  for (s in Solvers.values()) {
    val info: SolverInfo? = SolverOverviewTable().getSolverInformation(s)
    if (info != null) {
      infos.add(info)
	  }
  }

  infos.sortBy { it.getName() } // alphabetical ordering

  val rowBuilder = RowBuilder()
  for (info in infos) {
    rowBuilder.addSolver(info)
  }
  println(rowBuilder)
}
