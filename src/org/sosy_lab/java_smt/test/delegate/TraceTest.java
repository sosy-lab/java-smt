/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test.delegate;

import static com.google.common.truth.Truth.assertThat;
import static org.sosy_lab.java_smt.api.FormulaType.BooleanType;

import com.google.common.collect.ImmutableList;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.converters.FileTypeConverter;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;

public class TraceTest {

  @Rule public TemporaryFolder tempDir = new TemporaryFolder();

  private SolverContext context;
  private FormulaManager mgr;
  private BooleanFormulaManager bmgr;
  private Path traceFile;

  @Before
  public void setUp() throws InvalidConfigurationException, IOException {
    traceFile = tempDir.newFile("trace.java").toPath();
    FileTypeConverter fileTypeConverter =
        FileTypeConverter.create(Configuration.defaultConfiguration());
    Configuration.getDefaultConverters().put(FileOption.class, fileTypeConverter);
    Configuration config =
        Configuration.builder()
            .setOption("solver.trace", "true")
            .setOption("solver.tracefile", traceFile.toString())
            .addConverter(FileOption.class, fileTypeConverter)
            .build();

    context =
        SolverContextFactory.createSolverContext(
            config,
            LogManager.createNullLogManager(),
            org.sosy_lab.common.ShutdownNotifier.createDummy(),
            Solvers.SMTINTERPOL);
    mgr = context.getFormulaManager();
    bmgr = mgr.getBooleanFormulaManager();
  }

  @After
  public void tearDown() {
    context.close();
  }

  @Test
  public void testTraceCreation() throws IOException {
    @SuppressWarnings("unused")
    var unused = bmgr.makeTrue();
    context.close();

    assertThat(Files.exists(traceFile)).isTrue();
    assertThat(Files.readAllLines(traceFile)).isNotEmpty();
  }

  @Test
  public void testMakeVariable() throws IOException {
    @SuppressWarnings("unused")
    var unused = mgr.makeVariable(BooleanType, "x");
    context.close();

    assertThat(Files.exists(traceFile)).isTrue();
    assertThat(Files.readAllLines(traceFile))
        .containsExactly(
            "var config = Configuration.builder().build();",
            "var logger = LogManager.createNullLogManager();",
            "var notifier = ShutdownNotifier.createDummy();",
            "var context = SolverContextFactory.createSolverContext(config, logger, notifier,"
                + " SolverContextFactory.Solvers.SMTINTERPOL);",
            "var mgr = context.getFormulaManager();",
            "var var0 = mgr.makeVariable(FormulaType.BooleanType, \"x\");",
            "context.close();");
  }

  @Test
  public void testTraceProverEnvironment() throws Exception {
    try (var prover = context.newProverEnvironment()) {
      prover.push(bmgr.makeTrue());
      @SuppressWarnings("unused")
      var unused = prover.isUnsat();
    }
    context.close();

    assertThat(Files.exists(traceFile)).isTrue();
    assertThat(Files.readAllLines(traceFile))
        .containsExactly(
            "var config = Configuration.builder().build();",
            "var logger = LogManager.createNullLogManager();",
            "var notifier = ShutdownNotifier.createDummy();",
            "var context = SolverContextFactory.createSolverContext(config, logger, notifier,"
                + " SolverContextFactory.Solvers.SMTINTERPOL);",
            "var mgr = context.getFormulaManager();",
            "var var0 = context.newProverEnvironment();",
            "var var1 = mgr.getBooleanFormulaManager().makeTrue();",
            "var var2 = var0.push(var1);",
            "var var3 = var0.isUnsat();",
            "var0.close();",
            "context.close();");
  }

  @Test
  public void testTraceModel() throws Exception {
    IntegerFormulaManager imgr = mgr.getIntegerFormulaManager();
    try (var prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(42)));
      assertThat(prover.isUnsat()).isFalse();
      try (var model = prover.getModel()) {
        assertThat(model).isNotNull();
        assertThat(model.asList()).hasSize(1);
      }
    }
    context.close();

    assertThat(Files.exists(traceFile)).isTrue();
    assertThat(Files.readAllLines(traceFile))
        .containsExactly(
            "var config = Configuration.builder().build();",
            "var logger = LogManager.createNullLogManager();",
            "var notifier = ShutdownNotifier.createDummy();",
            "var context = SolverContextFactory.createSolverContext(config, logger, notifier,"
                + " SolverContextFactory.Solvers.SMTINTERPOL);",
            "var mgr = context.getFormulaManager();",
            "var var0 = context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS);",
            "var var1 = mgr.getIntegerFormulaManager().makeVariable(\"x\");",
            "var var2 = mgr.getIntegerFormulaManager().makeNumber(42);",
            "var var3 = mgr.getIntegerFormulaManager().equal(var1, var2);",
            "var var4 = var0.push(var3);",
            "var var5 = var0.isUnsat();",
            "var var6 = var0.getModel();",
            "var6.close();",
            "var0.close();",
            "context.close();");
  }

  @Test
  public void testTraceUFManager() throws Exception {
    var uf =
        mgr.getUFManager()
            .declareUF("f", FormulaType.BooleanType, ImmutableList.of(FormulaType.BooleanType));
    @SuppressWarnings("unused")
    var unused = mgr.getUFManager().callUF(uf, ImmutableList.of(bmgr.makeTrue()));
    context.close();

    assertThat(Files.exists(traceFile)).isTrue();
    assertThat(Files.readAllLines(traceFile))
        .containsExactly(
            "var config = Configuration.builder().build();",
            "var logger = LogManager.createNullLogManager();",
            "var notifier = ShutdownNotifier.createDummy();",
            "var context = SolverContextFactory.createSolverContext(config, logger, notifier,"
                + " SolverContextFactory.Solvers.SMTINTERPOL);",
            "var mgr = context.getFormulaManager();",
            "var var0 = mgr.getUFManager().declareUF(\"f\", FormulaType.BooleanType,"
                + " ImmutableList.of(FormulaType.BooleanType));",
            "var var1 = mgr.getBooleanFormulaManager().makeTrue();",
            "var var2 = mgr.getUFManager().callUF(var0, ImmutableList.of(var1));",
            "context.close();");
  }

  @Test
  public void testVisitor() throws Exception {
    IntegerFormulaManager imgr = mgr.getIntegerFormulaManager();
    BooleanFormula query = imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(42));
    @SuppressWarnings("unused")
    Formula query2 =
        mgr.visit(
            query,
            new DefaultFormulaVisitor<>() {
              @Override
              protected Formula visitDefault(Formula f) {
                return f;
              }
            });

    assertThat(Files.exists(traceFile)).isTrue();
    assertThat(Files.readAllLines(traceFile))
        .containsExactly(
            "var config = Configuration.builder().build();",
            "var logger = LogManager.createNullLogManager();",
            "var notifier = ShutdownNotifier.createDummy();",
            "var context = SolverContextFactory.createSolverContext(config, logger, notifier,"
                + " SolverContextFactory.Solvers.SMTINTERPOL);",
            "var mgr = context.getFormulaManager();",
            "var var0 = mgr.getIntegerFormulaManager().makeVariable(\"x\");",
            "var var1 = mgr.getIntegerFormulaManager().makeNumber(42);",
            "var var2 = mgr.getIntegerFormulaManager().equal(var0, var1);");
  }
}
