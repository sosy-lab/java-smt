/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import com.google.common.base.Joiner;
import com.google.common.base.Splitter;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableMap;
import com.google.common.io.MoreFiles;
import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.Map.Entry;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathTemplate;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;

@Options
public class TraceSolverContext implements SolverContext {
  private final SolverContext delegate;
  private final TraceLogger logger;
  private final TraceFormulaManager mgr;

  @Option(
      secure = true,
      name = "solver.tracefile",
      description = "Export solver interaction as Java code into a file.")
  @FileOption(FileOption.Type.OUTPUT_FILE)
  private @Nullable PathTemplate tracefileTemplate =
      PathTemplate.ofFormatString("traces/trace_%s.java");

  public TraceSolverContext(Solvers pSolver, Configuration config, SolverContext pDelegate)
      throws InvalidConfigurationException {
    config.inject(this);
    delegate = pDelegate;
    mgr = new TraceFormulaManager(delegate.getFormulaManager());

    // initialize the trace logger and create the trace file,
    // nanotime is used to avoid collisions, and it is sorted by time.
    final Path tracefile = tracefileTemplate.getPath(String.valueOf(System.nanoTime()));
    try {
      MoreFiles.createParentDirectories(tracefile);
    } catch (IOException e) {
      throw new InvalidConfigurationException("Could not create directory for trace files", e);
    }
    logger = new TraceLogger(mgr, tracefile.toFile());

    this.initializeJavaSMT(config, pSolver);
  }

  /** Write the header code for using JavaSMT, e.g., to initialize the context and solver. */
  private void initializeJavaSMT(Configuration config, Solvers pSolver) {
    // Get relevant options from the configuration
    String props = config.asPropertiesString();
    ImmutableMap.Builder<String, String> options = ImmutableMap.builder();
    for (String s : props.lines().toArray(String[]::new)) {
      List<String> parts = Splitter.on(" = ").splitToList(s);
      if (parts.get(0).startsWith("solver")
          && !parts.get(0).equals("solver.trace")
          && !parts.get(0).equals("solver.solver")) {
        options.put(parts.get(0), parts.get(1));
      }
    }

    // Write code for creating a solver context to the trace log
    logger.appendDef(
        "config",
        "Configuration.builder()"
            + FluentIterable.from(options.buildOrThrow().entrySet())
                .transform(
                    (Entry<String, String> e) ->
                        String.format(".setOption(\"%s\", \"%s\")", e.getKey(), e.getValue()))
                .join(Joiner.on(""))
            + ".build()");
    logger.appendDef("logger", "LogManager.createNullLogManager()");
    logger.appendDef("notifier", "ShutdownNotifier.createDummy()");
    logger.appendDef(
        "context",
        "SolverContextFactory.createSolverContext(config, logger, notifier, "
            + "SolverContextFactory.Solvers."
            + pSolver.name()
            + ")");
    logger.appendDef("mgr", "context.getFormulaManager()");
  }

  @Override
  public FormulaManager getFormulaManager() {
    return mgr;
  }

  @SuppressWarnings("resource")
  @Override
  public ProverEnvironment newProverEnvironment(ProverOptions... options) {
    return logger.logDefKeep(
        "context",
        String.format(
            "newProverEnvironment(%s)",
            FluentIterable.from(options)
                .transform(v -> "SolverContext" + ".ProverOptions." + v.name())
                .join(Joiner.on(", "))),
        () -> new TraceProverEnvironment(delegate.newProverEnvironment(options), mgr, logger));
  }

  @SuppressWarnings("resource")
  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... options) {
    throw new UnsupportedOperationException();
  }

  @SuppressWarnings("resource")
  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(ProverOptions... options) {
    throw new UnsupportedOperationException();
  }

  @Override
  public String getVersion() {
    return delegate.getVersion();
  }

  @Override
  public Solvers getSolverName() {
    return delegate.getSolverName();
  }

  @Override
  public void close() {
    logger.logStmt("context", "close()", delegate::close);
  }
}
