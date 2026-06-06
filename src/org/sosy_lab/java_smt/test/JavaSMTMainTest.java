/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import java.util.Map;
import org.junit.Test;
import org.sosy_lab.java_smt.cmdline.CmdLineArguments;
import org.sosy_lab.java_smt.cmdline.InvalidCmdlineArgumentException;

public class JavaSMTMainTest {

  @Test
  public void testProcessArgumentsWithSolverAndFile() throws Exception {
    Map<String, String> result =
        CmdLineArguments.processArguments(new String[] {"--solver", "Z3", "test.smt2"});
    assertThat(result.get("solver.solver")).isEqualTo("Z3");
    assertThat(result.get("smt2.file")).isEqualTo("test.smt2");
  }

  @Test
  public void testProcessArgumentsSolverShortFlag() throws Exception {
    Map<String, String> result =
        CmdLineArguments.processArguments(new String[] {"-solver", "SMTINTERPOL", "file.smt2"});
    assertThat(result.get("solver.solver")).isEqualTo("SMTINTERPOL");
  }

  @Test
  public void testProcessArgumentsHelp() throws Exception {
    Map<String, String> result = CmdLineArguments.processArguments(new String[] {"--help"});
    assertThat(result).containsKey("help");
  }

  @Test
  public void testProcessArgumentsHelpShortFlag() throws Exception {
    Map<String, String> result = CmdLineArguments.processArguments(new String[] {"-h"});
    assertThat(result).containsKey("help");
  }

  @Test
  public void testProcessArgumentsOnlyFile() throws Exception {
    Map<String, String> result = CmdLineArguments.processArguments(new String[] {"input.smt2"});
    assertThat(result.get("smt2.file")).isEqualTo("input.smt2");
  }

  @Test(expected = InvalidCmdlineArgumentException.class)
  public void testProcessArgumentsMultipleFiles() throws Exception {
    CmdLineArguments.processArguments(new String[] {"file1.smt2", "file2.smt2"});
  }

  @Test(expected = InvalidCmdlineArgumentException.class)
  public void testProcessArgumentsUnknownArgument() throws Exception {
    CmdLineArguments.processArguments(new String[] {"--unknown", "file.smt2"});
  }

  @Test(expected = InvalidCmdlineArgumentException.class)
  public void testProcessArgumentsSolverMissingValue() throws Exception {
    CmdLineArguments.processArguments(new String[] {"--solver"});
  }

  @Test
  public void testProcessArgumentsFileBeforeSolver() throws Exception {
    Map<String, String> result =
        CmdLineArguments.processArguments(new String[] {"test.smt2", "--solver", "Z3"});
    assertThat(result.get("smt2.file")).isEqualTo("test.smt2");
    assertThat(result.get("solver.solver")).isEqualTo("Z3");
  }

  @Test
  public void testProcessArgumentsDefaultSolver() throws Exception {
    Map<String, String> result = CmdLineArguments.processArguments(new String[] {"test.smt2"});
    assertThat(result.get("smt2.file")).isEqualTo("test.smt2");
    assertThat(result.get("solver.solver")).isNull();
  }

  @Test
  public void testProcessArgumentsWithLogic() throws Exception {
    Map<String, String> result =
        CmdLineArguments.processArguments(new String[] {"--logic", "QF_LIA", "test.smt2"});
    assertThat(result.get("solver.opensmt.logic")).isEqualTo("QF_LIA");
    assertThat(result.get("smt2.file")).isEqualTo("test.smt2");
  }

  @Test
  public void testProcessArgumentsWithLogicShortFlag() throws Exception {
    Map<String, String> result =
        CmdLineArguments.processArguments(new String[] {"-logic", "QF_UF", "test.smt2"});
    assertThat(result.get("solver.opensmt.logic")).isEqualTo("QF_UF");
  }

  @Test
  public void testProcessArgumentsWithSolverAndLogic() throws Exception {
    Map<String, String> result =
        CmdLineArguments.processArguments(
            new String[] {"--solver", "OPENSMT", "--logic", "QF_LIA", "test.smt2"});
    assertThat(result.get("solver.solver")).isEqualTo("OPENSMT");
    assertThat(result.get("solver.opensmt.logic")).isEqualTo("QF_LIA");
    assertThat(result.get("smt2.file")).isEqualTo("test.smt2");
  }

  @Test(expected = InvalidCmdlineArgumentException.class)
  public void testProcessArgumentsLogicMissingValue() throws Exception {
    CmdLineArguments.processArguments(new String[] {"--logic"});
  }
}
