/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
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
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathTemplate;
import org.sosy_lab.common.log.LogManager;
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

  public TraceSolverContext(
      Solvers pSolver, Configuration config, SolverContext pDelegate, LogManager pLogManager)
      throws InvalidConfigurationException {
    config.inject(this);
    delegate = pDelegate;
    mgr = new TraceFormulaManager(delegate.getFormulaManager(), pLogManager);

    // initialize the trace logger and create the trace file,
    // nanotime is used to avoid collisions, and it is sorted by time.
    final Path tracefile = tracefileTemplate.getPath(String.valueOf(System.nanoTime()));
    try {
      MoreFiles.createParentDirectories(tracefile);
    } catch (IOException e) {
      throw new InvalidConfigurationException("Could not create directory for trace files", e);
    }
    logger = new TraceLogger(mgr, tracefile);

    this.initializeJavaSMT(config, pSolver);
  }

  /** Write the header code for using JavaSMT, e.g., to initialize the context and solver. */
  private void initializeJavaSMT(Configuration config, Solvers pSolver) {
    Map<String, String> configurationOptions = getOptionsForTracing(config);

    // Write code for creating a solver context to the trace log
    logger.appendDef(
        "config",
        "Configuration.builder()"
            + FluentIterable.from(configurationOptions.entrySet())
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

  private ImmutableMap<String, String> getOptionsForTracing(Configuration config) {
    ImmutableMap.Builder<String, String> options = ImmutableMap.builder();

    // convert the configuration to a map of options, aka reverse Configuration#asPropertiesString.
    // TODO kind of expensive, but the configuration does not support this directly
    Map<String, String> properties =
        Splitter.on("\n")
            .trimResults()
            .omitEmptyStrings()
            .withKeyValueSeparator(" = ")
            .split(config.asPropertiesString());

    // filtering for those properties that start with "solver" (relevant for JavaSMT),
    // exclude trace-related properties.
    Set<String> traceConfigKeys = Set.of("solver.trace", "solver.tracefile", "solver.solver");
    for (Entry<String, String> entry : properties.entrySet()) {
      if (entry.getKey().startsWith("solver") && !traceConfigKeys.contains(entry.getKey())) {
        options.put(entry.getKey(), entry.getValue());
      }
    }

    return options.buildOrThrow();
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
        String.format("newProverEnvironment(%s)", getOptionsForLogging(options)),
        () -> new TraceProverEnvironment(delegate.newProverEnvironment(options), mgr, logger));
  }

  @SuppressWarnings("resource")
  @Override
  public InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation(
      ProverOptions... options) {
    return logger.logDefKeep(
        "context",
        String.format("newProverEnvironmentWithInterpolation(%s)", getOptionsForLogging(options)),
        () ->
            new TraceInterpolatingProverEnvironment<>(
                delegate.newProverEnvironmentWithInterpolation(options), mgr, logger));
  }

  @SuppressWarnings("resource")
  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment(ProverOptions... options) {
    return logger.logDefKeep(
        "context",
        String.format("newOptimizationProverEnvironment(%s)", getOptionsForLogging(options)),
        () ->
            new TraceOptimizationProverEnvironment(
                delegate.newOptimizationProverEnvironment(options), mgr, logger));
  }

  private static String getOptionsForLogging(ProverOptions[] options) {
    return FluentIterable.from(options)
        .transform(v -> "SolverContext.ProverOptions." + v.name())
        .join(Joiner.on(", "));
  }

  @Override
  public String getVersion() {
    return logger.logDefDiscard("context", "getVersion()", delegate::getVersion);
  }

  @Override
  public Solvers getSolverName() {
    return delegate.getSolverName();
  }

  @Override
  public void close() {
    if (!logger.isClosed()) { // avoid logging if already closed
      logger.logStmt("context", "close()", delegate::close);
    }
    logger.close();
  }
}
