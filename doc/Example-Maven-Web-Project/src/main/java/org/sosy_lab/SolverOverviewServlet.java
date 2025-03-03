// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab;

import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import java.io.IOException;
import java.io.PrintWriter;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.example.SolverOverviewTable.RowBuilder;
import org.sosy_lab.java_smt.example.SolverOverviewTable.SolverInfo;

/** Servlet implementation class SolverOverviewServlet */
@WebServlet("/SolverOverviewServlet")
public class SolverOverviewServlet extends HttpServlet {
  private static final long serialVersionUID = 1L;

  /** @see HttpServlet#HttpServlet() */
  public SolverOverviewServlet() {
    super();
  }

  /** @see HttpServlet#doGet(HttpServletRequest request, HttpServletResponse response) */
  protected void doGet(HttpServletRequest request, HttpServletResponse response)
      throws ServletException, IOException {
    response.getWriter().append("Served at: ").append(request.getContextPath());
    response.getWriter().println("\nThis is a test for JavaSMT.\n");

    try {
      SolverInfoPrinter printer = new SolverInfoPrinter();
      printer.printSolverInformation(response.getWriter());
    } catch (Exception e) {
      response.getWriter().println("\nException");
      response.getWriter().println(e.getMessage());
    }
  }

  /** @see HttpServlet#doPost(HttpServletRequest request, HttpServletResponse response) */
  protected void doPost(HttpServletRequest request, HttpServletResponse response)
      throws ServletException, IOException {
    doGet(request, response);
  }

  public class SolverInfoPrinter {

    public void printSolverInformation(PrintWriter out)
        throws InterruptedException, SolverException {

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
      out.println(rowBuilder);
    }
  }
}
