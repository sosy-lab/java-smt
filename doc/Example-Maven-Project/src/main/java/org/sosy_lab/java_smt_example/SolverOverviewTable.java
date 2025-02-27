// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt_example;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.example.SolverOverviewTable.RowBuilder;
import org.sosy_lab.java_smt.example.SolverOverviewTable.SolverInfo;

/**
 * This program takes all installed solvers and checks them for version, theories and features and
 * prints them to StdOut in a nice table.
 *
 * <p>This is just a copy of org.sosy_lab.java_smt.example.SolverOverviewTable
 */
public class SolverOverviewTable {

  public static void main(String[] args) throws SolverException, InterruptedException {

    final org.sosy_lab.java_smt.example.SolverOverviewTable infoProvider =
        new org.sosy_lab.java_smt.example.SolverOverviewTable();
    final List<SolverInfo> infos = new ArrayList<>();
    for (Solvers s : Solvers.values()) {
      infos.add(infoProvider.getSolverInformation(s));
    }
    infos.sort(Comparator.comparing(SolverInfo::getName)); // alphabetical ordering

    RowBuilder rowBuilder = new RowBuilder();
    for (SolverInfo info : infos) {
      rowBuilder.addSolver(info);
    }
    System.out.println(rowBuilder);
  }

  private SolverOverviewTable() {}
}
