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
import java.io.IOException;
import java.util.List;
import java.util.Map.Entry;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;

public class TraceSolverContext implements SolverContext {
  private final SolverContext delegate;
  private final TraceLogger logger;

  public TraceSolverContext(SolverContext pDelegate, Configuration config) {
    delegate = pDelegate;
    // FIXME Move the files to the output folder?
    logger =
        new TraceLogger(
            "trace" + Integer.toUnsignedString(System.identityHashCode(this)) + ".java");

    // Get relevant options from the configuration
    String props = config.asPropertiesString();
    ImmutableMap.Builder<String, String> options = ImmutableMap.builder();
    for (String s : props.lines().toArray(String[]::new)) {
      List<String> parts = Splitter.on(" = ").splitToList(s);
      ;
      if (parts.get(0).startsWith("solver") && !parts.get(0).equals("solver.trace")) {
        options.put(parts.get(0), parts.get(1));
      }
    }

    // Write code for creating a solver context to the trace log
    try {
      logger.appendDef(
          "config",
          "Configuration.builder()."
              + FluentIterable.from(options.build().entrySet())
                  .transform(
                      (Entry<String, String> e) ->
                          String.format("setOption(\"%s\", \"%s\")", e.getKey(), e.getValue()))
                  .join(Joiner.on("."))
              + ".build()");
      logger.appendDef("logger", "LogManager.createNullLogManager()");
      logger.appendDef("notifier", "ShutdownNotifier.createDummy()");
      logger.appendDef(
          "context", "SolverContextFactory.createSolverContext(config, logger, notifier)");
      logger.appendDef("mgr", "context.getFormulaManager()");
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  @Override
  public FormulaManager getFormulaManager() {
    return new TraceFormulaManager(delegate.getFormulaManager(), logger);
  }

  @SuppressWarnings("resource")
  @Override
  public ProverEnvironment newProverEnvironment(ProverOptions... options) {
    return logger.logDef(
        "context",
        String.format(
            "newProverEnvironment(%s)",
            FluentIterable.from(options)
                .transform(v -> "SolverContext" + ".ProverOptions." + v.name())
                .join(Joiner.on(", "))),
        () -> new TraceProverEnvironment(delegate.newProverEnvironment(options), logger));
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
