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
import static org.junit.Assert.assertThrows;

import com.google.common.collect.ImmutableList;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
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

  private static final String NL = System.lineSeparator();
  private static final String SOLVER = "--solver";
  private static final String SMTINTERPOL = "SMTINTERPOL";
  private static final String PRINCESS = "PRINCESS";

  @Rule public TemporaryFolder tempDir = new TemporaryFolder();

  /** The result of one invocation of the command-line interface. */
  private record Run(int exitCode, String out, String err) {}

  /** Runs the command-line interface in-process, capturing stdout and stderr. */
  private static Run run(String... args) {
    return run(ShutdownNotifier.createDummy(), args);
  }

  private static Run run(ShutdownNotifier shutdownNotifier, String... args) {
    StringBuilder out = new StringBuilder();
    StringBuilder err = new StringBuilder();
    int exitCode = JavaSMTMain.run(args, out, err, shutdownNotifier);
    return new Run(exitCode, out.toString(), err.toString());
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
    Run r = run(SOLVER, SMTINTERPOL, smt2File(SAT_INPUT));
    assertThat(r.out()).isEqualTo("sat" + NL);
    assertThat(r.exitCode()).isEqualTo(0);
  }

  @Test
  public void testRunUnsatWithSeveralAssertions() throws IOException {
    Run r = run(SOLVER, PRINCESS, smt2File(UNSAT_INPUT));
    assertThat(r.out()).isEqualTo("unsat" + NL);
    assertThat(r.exitCode()).isEqualTo(0);
  }

  @Test
  public void testRunDefaultSolverIsSmtInterpol() throws IOException {
    Run r = run(smt2File(UNSAT_INPUT));
    assertThat(r.out()).isEqualTo("unsat" + NL);
    assertThat(r.exitCode()).isEqualTo(0);
    assertThat(r.err()).isEmpty();
  }

  @Test
  public void testRunSolverNameIsCaseInsensitive() throws IOException {
    Run r = run(SOLVER, "smtinterpol", smt2File(SAT_INPUT));
    assertThat(r.out()).isEqualTo("sat" + NL);
    assertThat(r.exitCode()).isEqualTo(0);
  }

  @Test
  public void testRunHelpTakesPrecedenceOverFile() throws IOException {
    Run r = run("--help", SOLVER, SMTINTERPOL, smt2File(SAT_INPUT));
    assertThat(r.out()).isNotEmpty();
    assertThat(r.out()).isNotEqualTo("sat" + NL);
    assertThat(r.err()).isEmpty();
    assertThat(r.exitCode()).isEqualTo(0);
  }

  @Test
  public void testRunWithoutArgumentsPrintsHelp() {
    Run r = run();
    assertThat(r.out()).isNotEmpty();
    assertThat(r.err()).isEmpty();
    assertThat(r.exitCode()).isEqualTo(0);
  }

  @Test
  public void testRunWithoutFileIsAnError() {
    Run r = run(SOLVER, SMTINTERPOL);
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunUnknownArgumentIsAnError() throws IOException {
    Run r = run("--unknown", smt2File(SAT_INPUT));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunUnknownSolverIsAnError() throws IOException {
    Run r = run(SOLVER, "NOSUCHSOLVER", smt2File(SAT_INPUT));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunMissingFileIsAnError() {
    Run r = run(SOLVER, SMTINTERPOL, tempDir.getRoot().toPath().resolve("missing.smt2").toString());
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunEmptyFileIsAnError() throws IOException {
    Run r = run(SOLVER, SMTINTERPOL, smt2File(""));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunFileWithoutCommandsIsAnError() throws IOException {
    Run r = run(SOLVER, SMTINTERPOL, smt2File("this is not an SMT2 file\n"));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunUnparsableFileIsAnError() throws IOException {
    // The parser would ignore the text and report sat for the (check-sat).
    Run r = run(SOLVER, SMTINTERPOL, smt2File("this is not an SMT2 file\n(check-sat)\n"));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunAssertionAfterCheckSatIsAnError() throws IOException {
    // parseAll collects all assertions, the answer would be unsat instead of sat.
    String input = "(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n(assert (< x 0))\n";
    Run r = run(SOLVER, SMTINTERPOL, smt2File(input));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunWithoutAssertionsIsSat() throws IOException {
    Run r = run(SOLVER, SMTINTERPOL, smt2File("(set-logic QF_LIA)\n(check-sat)\n"));
    assertThat(r.out()).isEqualTo("sat" + NL);
    assertThat(r.exitCode()).isEqualTo(0);
  }

  @Test
  public void testRunUnbalancedParenthesesIsAnError() throws IOException {
    Run r = run(SOLVER, SMTINTERPOL, smt2File("(declare-fun x () Int)\n(assert (> x 0)\n"));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunUndeclaredSymbolIsAnError() throws IOException {
    Run r = run(SOLVER, SMTINTERPOL, smt2File("(assert (> y 0))\n(check-sat)\n"));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunTypeErrorIsAnError() throws IOException {
    Run r =
        run(
            SOLVER,
            PRINCESS,
            smt2File("(declare-fun x () Int)\n(assert (> x true))\n(check-sat)\n"));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunTwoCheckSatsIsAnError() throws IOException {
    String input = "(declare-fun x () Int)\n(assert (> x 0))\n(check-sat)\n(check-sat)\n";
    Run r = run(SOLVER, SMTINTERPOL, smt2File(input));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunCheckSatAssumingIsAnError() throws IOException {
    // parseAll ignores (check-sat-assuming ...), the answer would be sat instead of unsat.
    String input = "(declare-fun p () Bool)\n(assert p)\n(check-sat-assuming ((not p)))\n";
    Run r = run(SOLVER, SMTINTERPOL, smt2File(input));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunMalformedCheckSatIsAnError() throws IOException {
    String input = "(declare-fun x () Int)\n(assert (> x 0))\n(check-sat 1)\n";
    Run r = run(SOLVER, SMTINTERPOL, smt2File(input));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunInvalidPathIsAnError() {
    Run r = run(SOLVER, SMTINTERPOL, "bad\0name.smt2");
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunPopIsAnError() throws IOException {
    String input = "(declare-fun x () Int)\n(assert (> x 0))\n(pop 1)\n(check-sat)\n";
    Run r = run(SOLVER, SMTINTERPOL, smt2File(input));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunResetIsAnError() throws IOException {
    String input = "(declare-fun x () Int)\n(assert (> x 0))\n(reset)\n(check-sat)\n";
    Run r = run(SOLVER, SMTINTERPOL, smt2File(input));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunResetAssertionsIsAnError() throws IOException {
    String input = "(declare-fun x () Int)\n(assert (> x 0))\n(reset-assertions)\n(check-sat)\n";
    Run r = run(SOLVER, SMTINTERPOL, smt2File(input));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunExitBeforeLastCommandIsAnError() throws IOException {
    String input = "(declare-fun x () Int)\n(assert (> x 0))\n(exit)\n(check-sat)\n";
    Run r = run(SOLVER, SMTINTERPOL, smt2File(input));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunPushIsAnError() throws IOException {
    String input = "(declare-fun x () Int)\n(push 1)\n(assert (> x 0))\n(check-sat)\n";
    Run r = run(SOLVER, SMTINTERPOL, smt2File(input));
    assertThat(r.out()).isEmpty();
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
  }

  @Test
  public void testRunLogicWithoutOpenSmtWarnsOnce() throws IOException {
    String file = smt2File(SAT_INPUT);
    Run r = run("--logic", "QF_LIA", SOLVER, SMTINTERPOL, file);
    assertThat(r.out()).isEqualTo("sat" + NL);
    assertThat(r.exitCode()).isEqualTo(0);
    assertThat(r.err()).isNotEmpty(); // the warning

    // Running again must not duplicate the log output of the first run.
    Run r2 = run("--logic", "QF_LIA", SOLVER, SMTINTERPOL, file);
    assertThat(r2.err()).isEqualTo(r.err());
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
    Run r = run(shutdown.getNotifier(), SOLVER, SMTINTERPOL, smt2File(UNSAT_INPUT));
    assertThat(r.out()).isEqualTo("unknown" + NL);
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
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
    Run r = run(shutdown.getNotifier(), SOLVER, SMTINTERPOL, smt2File(pigeonholeInput(12)));
    requester.join();
    assertThat(r.out()).isEqualTo("unknown" + NL);
    assertThat(r.err()).isNotEmpty();
    assertThat(r.exitCode()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
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
                ImmutableList.of(
                    Path.of(System.getProperty("java.home"), "bin", "java").toString(),
                    "-cp",
                    System.getProperty("java.class.path"),
                    JavaSMTMain.class.getName(),
                    SOLVER,
                    SMTINTERPOL,
                    smt2File(pigeonholeInput(12))))
            .redirectOutput(outFile.toFile())
            .redirectError(ProcessBuilder.Redirect.DISCARD)
            .start();
    try {
      Thread.sleep(3000); // let the JVM start and the solver run
      process.destroy();
      assertThat(process.waitFor(30, TimeUnit.SECONDS)).isTrue();

      assertThat(Files.readString(outFile)).isEqualTo("unknown" + NL);
      // The JVM exits with 128 + signal number after running the shutdown hooks.
      assertThat(process.exitValue()).isEqualTo(128 + 15);
    } finally {
      process.destroyForcibly();
    }
  }

  @Test(timeout = 60_000)
  public void testMainReportsFailureToWriteResult() throws Exception {
    Path devFull = Path.of("/dev/full");
    assume().withMessage("/dev/full is not available").that(Files.exists(devFull)).isTrue();

    Process process =
        new ProcessBuilder(
                ImmutableList.of(
                    Path.of(System.getProperty("java.home"), "bin", "java").toString(),
                    "-cp",
                    System.getProperty("java.class.path"),
                    JavaSMTMain.class.getName(),
                    SOLVER,
                    SMTINTERPOL,
                    smt2File(SAT_INPUT)))
            .redirectOutput(devFull.toFile())
            .redirectError(ProcessBuilder.Redirect.DISCARD)
            .start();
    try {
      assertThat(process.waitFor(30, TimeUnit.SECONDS)).isTrue();
      assertThat(process.exitValue()).isEqualTo(JavaSMTMain.ERROR_EXIT_CODE);
    } finally {
      process.destroyForcibly();
    }
  }

  // Tests for the argument parsing.

  @Test
  public void testProcessArgumentsWithSolverAndFile() throws Exception {
    Map<String, String> result =
        CmdLineArguments.processArguments(new String[] {SOLVER, "Z3", "test.smt2"});
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

  @Test
  public void testProcessArgumentsMultipleFiles() {
    assertThrows(
        InvalidCmdlineArgumentException.class,
        () -> CmdLineArguments.processArguments(new String[] {"file1.smt2", "file2.smt2"}));
  }

  @Test
  public void testProcessArgumentsUnknownArgument() {
    assertThrows(
        InvalidCmdlineArgumentException.class,
        () -> CmdLineArguments.processArguments(new String[] {"--unknown", "file.smt2"}));
  }

  @Test
  public void testProcessArgumentsSolverMissingValue() {
    assertThrows(
        InvalidCmdlineArgumentException.class,
        () -> CmdLineArguments.processArguments(new String[] {SOLVER}));
  }

  @Test
  public void testProcessArgumentsFileBeforeSolver() throws Exception {
    Map<String, String> result =
        CmdLineArguments.processArguments(new String[] {"test.smt2", SOLVER, "Z3"});
    assertThat(result.get("smt2.file")).isEqualTo("test.smt2");
    assertThat(result.get("solver.solver")).isEqualTo("Z3");
  }

  @Test
  public void testProcessArgumentsWithoutSolverLeavesSolverUnset() throws Exception {
    Map<String, String> result = CmdLineArguments.processArguments(new String[] {"test.smt2"});
    assertThat(result.get("smt2.file")).isEqualTo("test.smt2");
    assertThat(result).doesNotContainKey("solver.solver");
  }

  @Test
  public void testProcessArgumentsWithLogic() throws Exception {
    Map<String, String> result =
        CmdLineArguments.processArguments(new String[] {"--logic", "QF_LIA", "test.smt2"});
    assertThat(result.get("solver.opensmt.logic")).isEqualTo("QF_LIA");
    assertThat(result.get("solver.z3.logic")).isEqualTo("QF_LIA");
    assertThat(result.get("smt2.file")).isEqualTo("test.smt2");
  }

  @Test
  public void testProcessArgumentsWithLogicShortFlag() throws Exception {
    Map<String, String> result =
        CmdLineArguments.processArguments(new String[] {"-logic", "QF_UF", "test.smt2"});
    assertThat(result.get("solver.opensmt.logic")).isEqualTo("QF_UF");
    assertThat(result.get("solver.z3.logic")).isEqualTo("QF_UF");
  }

  @Test
  public void testProcessArgumentsWithSolverAndLogic() throws Exception {
    Map<String, String> result =
        CmdLineArguments.processArguments(
            new String[] {SOLVER, "OPENSMT", "--logic", "QF_LIA", "test.smt2"});
    assertThat(result.get("solver.solver")).isEqualTo("OPENSMT");
    assertThat(result.get("solver.opensmt.logic")).isEqualTo("QF_LIA");
    assertThat(result.get("solver.z3.logic")).isEqualTo("QF_LIA");
    assertThat(result.get("smt2.file")).isEqualTo("test.smt2");
  }

  @Test
  public void testProcessArgumentsLogicMissingValue() {
    assertThrows(
        InvalidCmdlineArgumentException.class,
        () -> CmdLineArguments.processArguments(new String[] {"--logic"}));
  }

  @Test
  public void testProcessArgumentsInvalidPath() {
    assertThrows(
        InvalidCmdlineArgumentException.class,
        () -> CmdLineArguments.processArguments(new String[] {"bad\0name.smt2"}));
  }
}
