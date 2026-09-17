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
import static com.google.common.truth.TruthJUnit.assume;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.concurrent.TimeUnit;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.cmdline.CmdLineArguments;
import org.sosy_lab.java_smt.cmdline.InvalidCmdlineArgumentException;
import org.sosy_lab.java_smt.cmdline.JavaSMTMain;

public class JavaSMTMainTest {

  private static final String SAT_INPUT =
      """
      (set-logic QF_LIA)
      (declare-fun x () Int)
      (assert (> x 0))
      (check-sat)
      (exit)
      """;

  private static final String UNSAT_INPUT =
      """
      (set-info :smt-lib-version 2.6)
      (set-logic QF_LIA)
      (declare-fun x () Int)
      (assert (> x 0))
      (assert (< x 0))
      (check-sat)
      """;

  @Rule public TemporaryFolder tempDir = new TemporaryFolder();

  /** The result of one invocation of the command-line interface. */
  private static final class Run {
    final int exitCode;
    final String out;
    final String err;

    Run(int pExitCode, String pOut, String pErr) {
      exitCode = pExitCode;
      out = pOut;
      err = pErr;
    }
  }

  /** Runs the command-line interface in-process, capturing stdout and stderr. */
  private static Run run(String... args) {
    return run(ShutdownNotifier.createDummy(), args);
  }

  private static Run run(ShutdownNotifier shutdownNotifier, String... args) {
    ByteArrayOutputStream outBytes = new ByteArrayOutputStream();
    ByteArrayOutputStream errBytes = new ByteArrayOutputStream();
    int exitCode;
    try (PrintStream out = new PrintStream(outBytes, true, StandardCharsets.UTF_8);
        PrintStream err = new PrintStream(errBytes, true, StandardCharsets.UTF_8)) {
      exitCode = JavaSMTMain.run(args, out, err, shutdownNotifier);
    }
    return new Run(
        exitCode,
        outBytes.toString(StandardCharsets.UTF_8),
        errBytes.toString(StandardCharsets.UTF_8));
  }

  private String smt2File(String content) throws IOException {
    Path file = Files.createTempFile(tempDir.getRoot().toPath(), "input", ".smt2");
    Files.writeString(file, content);
    return file.toString();
  }

  // Tests for the whole command-line interface.
  // Only the pure-Java solvers SMTInterpol and Princess are used, so that these tests can run on
  // every platform without native libraries.

  @Test
  public void testRunSat() throws IOException {
    Run r = run("--solver", "SMTINTERPOL", smt2File(SAT_INPUT));
    assertThat(r.out).isEqualTo("sat\n");
    assertThat(r.exitCode).isEqualTo(0);
  }

  @Test
  public void testRunUnsatWithSeveralAssertions() throws IOException {
    Run r = run("--solver", "PRINCESS", smt2File(UNSAT_INPUT));
    assertThat(r.out).isEqualTo("unsat\n");
    assertThat(r.exitCode).isEqualTo(0);
  }

  @Test
  public void testRunDefaultSolverIsSmtInterpol() throws IOException {
    Run r = run(smt2File(UNSAT_INPUT));
    assertThat(r.out).isEqualTo("unsat\n");
    assertThat(r.exitCode).isEqualTo(0);
    assertThat(r.err).isEmpty();
  }

  @Test
  public void testRunSolverNameIsCaseInsensitive() throws IOException {
    Run r = run("--solver", "smtinterpol", smt2File(SAT_INPUT));
    assertThat(r.out).isEqualTo("sat\n");
    assertThat(r.exitCode).isEqualTo(0);
  }

  @Test
  public void testRunHelpTakesPrecedenceOverFile() throws IOException {
    Run r = run("--help", "--solver", "SMTINTERPOL", smt2File(SAT_INPUT));
    assertThat(r.out).contains("Usage: javasmt");
    assertThat(r.out).doesNotContain("sat\n");
    assertThat(r.exitCode).isEqualTo(0);
  }

  @Test
  public void testRunWithoutArgumentsPrintsHelp() {
    Run r = run();
    assertThat(r.out).contains("Usage: javasmt");
    assertThat(r.exitCode).isEqualTo(0);
  }

  @Test
  public void testRunWithoutFileIsAnError() {
    Run r = run("--solver", "SMTINTERPOL");
    assertThat(r.out).isEmpty();
    assertThat(r.err).contains("No SMT2 file given");
    assertThat(r.exitCode).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunUnknownArgumentIsAnError() throws IOException {
    Run r = run("--unknown", smt2File(SAT_INPUT));
    assertThat(r.out).isEmpty();
    assertThat(r.err).contains("Unknown command-line argument: --unknown");
    assertThat(r.exitCode).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunUnknownSolverIsAnError() throws IOException {
    Run r = run("--solver", "NOSUCHSOLVER", smt2File(SAT_INPUT));
    assertThat(r.out).isEmpty();
    assertThat(r.err).contains("Invalid configuration");
    assertThat(r.exitCode).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunMissingFileIsAnError() {
    Run r = run("--solver", "SMTINTERPOL", tempDir.getRoot().toPath().resolve("missing.smt2").toString());
    assertThat(r.out).isEmpty();
    assertThat(r.err).contains("Could not read SMT2 file");
    assertThat(r.exitCode).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunEmptyFileIsAnError() throws IOException {
    Run r = run("--solver", "SMTINTERPOL", smt2File(""));
    assertThat(r.out).isEmpty();
    assertThat(r.err).contains("no (check-sat) command");
    assertThat(r.exitCode).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunUnparsableFileIsAnError() throws IOException {
    Run r = run("--solver", "SMTINTERPOL", smt2File("this is not an SMT2 file\n"));
    assertThat(r.out).isEmpty();
    assertThat(r.err).contains("no (check-sat) command");
    assertThat(r.exitCode).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunWithoutAssertionsIsSat() throws IOException {
    Run r = run("--solver", "SMTINTERPOL", smt2File("(set-logic QF_LIA)\n(check-sat)\n"));
    assertThat(r.out).isEqualTo("sat\n");
    assertThat(r.exitCode).isEqualTo(0);
  }

  @Test
  public void testRunUnbalancedParenthesesIsAnError() throws IOException {
    Run r = run("--solver", "SMTINTERPOL", smt2File("(declare-fun x () Int)\n(assert (> x 0)\n"));
    assertThat(r.out).isEmpty();
    assertThat(r.err).contains("Could not parse SMT2 file");
    assertThat(r.err).doesNotContain("Exception in thread");
    assertThat(r.exitCode).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunUndeclaredSymbolIsAnError() throws IOException {
    Run r = run("--solver", "SMTINTERPOL", smt2File("(assert (> y 0))\n(check-sat)\n"));
    assertThat(r.out).isEmpty();
    assertThat(r.err).contains("Could not parse SMT2 file with SMTINTERPOL");
    assertThat(r.err).doesNotContain("Exception in thread");
    assertThat(r.exitCode).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunTypeErrorIsAnError() throws IOException {
    Run r =
        run(
            "--solver",
            "PRINCESS",
            smt2File("(declare-fun x () Int)\n(assert (> x true))\n(check-sat)\n"));
    assertThat(r.out).isEmpty();
    assertThat(r.err).contains("Could not parse SMT2 file with PRINCESS");
    assertThat(r.exitCode).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunUnsupportedCommandIsAnError() throws IOException {
    String input = "(declare-fun x () Int)\n(push 1)\n(assert (> x 0))\n(check-sat)\n";
    Run r = run("--solver", "SMTINTERPOL", smt2File(input));
    assertThat(r.out).isEmpty();
    assertThat(r.err).contains("Could not parse SMT2 file");
    assertThat(r.err).contains("(push ...)");
    assertThat(r.exitCode).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunLogicWithoutOpenSmtWarnsOnce() throws IOException {
    Run r = run("--logic", "QF_LIA", "--solver", "SMTINTERPOL", smt2File(SAT_INPUT));
    assertThat(r.out).isEqualTo("sat\n");
    assertThat(r.exitCode).isEqualTo(0);
    assertThat(r.err).contains("Option --logic is only effective with OpenSMT");
    assertThat(r.err.indexOf("--logic")).isEqualTo(r.err.lastIndexOf("--logic"));

    // Running again must not duplicate the log output of the first run.
    Run r2 = run("--logic", "QF_LIA", "--solver", "SMTINTERPOL", smt2File(SAT_INPUT));
    assertThat(r2.err.indexOf("--logic")).isEqualTo(r2.err.lastIndexOf("--logic"));
  }

  /**
   * The pigeonhole principle for the given number of holes, an unsatisfiable propositional problem
   * that takes resolution-based solvers exponential time. Used as input that does not terminate
   * within the time of a test.
   */
  private static String pigeonholeInput(int holes) {
    int pigeons = holes + 1;
    StringBuilder sb = new StringBuilder("(set-logic QF_UF)\n");
    for (int p = 0; p < pigeons; p++) {
      for (int h = 0; h < holes; h++) {
        sb.append("(declare-const p").append(p).append("h").append(h).append(" Bool)\n");
      }
    }
    for (int p = 0; p < pigeons; p++) { // every pigeon is in some hole
      sb.append("(assert (or");
      for (int h = 0; h < holes; h++) {
        sb.append(" p").append(p).append("h").append(h);
      }
      sb.append("))\n");
    }
    for (int h = 0; h < holes; h++) { // no two pigeons share a hole
      for (int p = 0; p < pigeons; p++) {
        for (int q = p + 1; q < pigeons; q++) {
          sb.append("(assert (not (and p").append(p).append("h").append(h);
          sb.append(" p").append(q).append("h").append(h).append(")))\n");
        }
      }
    }
    sb.append("(check-sat)\n");
    return sb.toString();
  }

  @Test
  public void testRunShutdownRequestedBeforeSolvingIsUnknown() throws IOException {
    ShutdownManager shutdown = ShutdownManager.create();
    shutdown.requestShutdown("requested by test");
    Run r = run(shutdown.getNotifier(), "--solver", "SMTINTERPOL", smt2File(UNSAT_INPUT));
    assertThat(r.out).isEqualTo("unknown\n");
    assertThat(r.err).contains("requested by test");
    assertThat(r.exitCode).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test(timeout = 60_000)
  public void testRunShutdownRequestedWhileSolvingIsUnknown() throws Exception {
    ShutdownManager shutdown = ShutdownManager.create();
    Thread requester =
        new Thread(
            () -> {
              try {
                Thread.sleep(500);
              } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
              }
              shutdown.requestShutdown("requested by test while solving");
            });
    requester.start();
    Run r = run(shutdown.getNotifier(), "--solver", "SMTINTERPOL", smt2File(pigeonholeInput(12)));
    requester.join();
    assertThat(r.out).isEqualTo("unknown\n");
    assertThat(r.err).contains("requested by test while solving");
    assertThat(r.exitCode).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test(timeout = 60_000)
  public void testMainReportsUnknownWhenTerminated() throws Exception {
    // Process.destroy() sends SIGTERM on Unix, which runs the shutdown hook of the JVM.
    // On Windows the process is killed immediately without running any hook.
    assume()
        .withMessage("SIGTERM cannot be sent on Windows")
        .that(System.getProperty("os.name").toLowerCase(Locale.ROOT).startsWith("win"))
        .isFalse();

    Path outFile = tempDir.newFile("stdout").toPath();
    Process process =
        new ProcessBuilder(
                List.of(
                    Path.of(System.getProperty("java.home"), "bin", "java").toString(),
                    "-cp",
                    System.getProperty("java.class.path"),
                    JavaSMTMain.class.getName(),
                    "--solver",
                    "SMTINTERPOL",
                    smt2File(pigeonholeInput(12))))
            .redirectOutput(outFile.toFile())
            .redirectError(ProcessBuilder.Redirect.DISCARD)
            .start();
    Thread.sleep(3000); // let the JVM start and the solver run
    process.destroy();
    assertThat(process.waitFor(30, TimeUnit.SECONDS)).isTrue();

    assertThat(Files.readString(outFile)).isEqualTo("unknown\n");
    assertThat(process.exitValue()).isNotEqualTo(0);
  }

  // Tests for the argument parsing.

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
