// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assert_;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;

import java.util.regex.Pattern;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.test.SolverBasedTest0.ParameterizedSolverBasedTest0;

/**
 * This JUnit test class is mainly intended for automated CI checks on different operating systems,
 * where a plain environment without pre-installed solvers is guaranteed.
 */
@RunWith(Parameterized.class)
public class SolverContextFactoryTest {
  protected Configuration config;
  protected final LogManager logger = LogManager.createTestLogManager();
  protected ShutdownManager shutdownManager = ShutdownManager.create();

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return ParameterizedSolverBasedTest0.getAllSolvers();
  }

  @Parameter(0)
  public Solvers solver;

  private Solvers solverToUse() {
    return solver;
  }

  private void requireNoNativeLibrary() {
    assume()
        .withMessage("Solver %s requires to load a native library", solverToUse())
        .that(solverToUse())
        .isAnyOf(Solvers.SMTINTERPOL, Solvers.PRINCESS);
  }

  private void requireNativeLibrary() {
    assume()
        .withMessage("Solver %s requires to load a native library", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.SMTINTERPOL, Solvers.PRINCESS);
  }

  /**
   * Let's allow to disable some checks on certain combinations of operating systems and solvers,
   * because of missing support.
   *
   * <p>We update this list, whenever a new solver or operating system is added.
   */
  private void requirePlatformSupported() {
    assume()
        .withMessage("Solver %s is not yet supported on this platform", solverToUse())
        .that(Solvers.available().contains(solverToUse()))
        .isTrue();
  }

  private void requirePlatformNotSupported() {
    assume()
        .withMessage("Solver %s is not yet supported on this platform", solverToUse())
        .that(Solvers.available().contains(solverToUse()))
        .isFalse();
  }

  @Before
  public final void initSolver() throws InvalidConfigurationException {
    config = Configuration.builder().setOption("solver.solver", solverToUse().toString()).build();
  }

  @Test
  public void createSolverContextFactoryWithDefaultLoader() throws InvalidConfigurationException {
    requirePlatformSupported();

    SolverContextFactory factory =
        new SolverContextFactory(config, logger, shutdownManager.getNotifier());
    try (SolverContext context = factory.generateContext()) {
      @SuppressWarnings("unused")
      FormulaManager mgr = context.getFormulaManager();
      checkVersion(context);
    }
  }

  @Test
  public void createSolverContextFactoryWithSystemLoader() throws InvalidConfigurationException {
    requireNativeLibrary();
    requirePlatformSupported();

    // we assume that no native solvers are installed on the testing machine by default.
    SolverContextFactory factory =
        new SolverContextFactory(
            config, logger, shutdownManager.getNotifier(), System::loadLibrary);
    assert_()
        .that(assertThrows(InvalidConfigurationException.class, factory::generateContext))
        .hasCauseThat()
        .isInstanceOf(UnsatisfiedLinkError.class);
  }

  @Test
  public void createSolverContextFactoryWithSystemLoaderForJavaSolver()
      throws InvalidConfigurationException {
    requireNoNativeLibrary();
    requirePlatformSupported();

    SolverContextFactory factory =
        new SolverContextFactory(
            config, logger, shutdownManager.getNotifier(), System::loadLibrary);
    try (SolverContext context = factory.generateContext()) {
      @SuppressWarnings("unused")
      FormulaManager mgr = context.getFormulaManager();
      checkVersion(context);
    }
  }

  /** Check whether each solver reports a nice and readable version string. */
  private void checkVersion(SolverContext pContext) {
    String solverName = solverToUse().toString();
    if (solverToUse() == Solvers.YICES2) {
      solverName = "YICES"; // remove the number "2" from the name
    } else if (solverToUse() == Solvers.Z3_WITH_INTERPOLATION) {
      solverName = "Z3";
    }
    String optionalSuffix = "([A-Za-z0-9.,:_+\\-\\s()@]+)?"; // any string
    String versionNumberRegex =
        "(version\\s)?\\d+\\.\\d+(\\.\\d+)?(\\.\\d+)?"; // 2-4 numbers with dots
    if (solverToUse() == Solvers.PRINCESS) {
      versionNumberRegex = "\\d+-\\d+-\\d+"; // Princess uses date instead of version
    }
    String versionRegex = solverName + "\\s+" + versionNumberRegex + optionalSuffix;
    Pattern versionPattern = Pattern.compile(versionRegex, Pattern.CASE_INSENSITIVE);
    assert_()
        .withMessage("Solver did not report a nice readable version number.")
        .that(pContext.getVersion())
        .matches(versionPattern);
  }

  /** Negative test for failing to load native library. */
  @Test
  public void testFailToLoadNativeLibraryWithInvalidOperatingSystem()
      throws InvalidConfigurationException {
    requireNativeLibrary();
    requirePlatformNotSupported();

    SolverContextFactory factory =
        new SolverContextFactory(config, logger, shutdownManager.getNotifier());

    // Verify that creating the context fails with UnsatisfiedLinkError
    InvalidConfigurationException thrown =
        assertThrows(
            "Expected InvalidConfigurationException due to failure in loading native library",
            InvalidConfigurationException.class,
            factory::generateContext);
    assert_().that(thrown).hasCauseThat().isInstanceOf(UnsatisfiedLinkError.class);
    assert_()
        .that(thrown)
        .hasMessageThat()
        .startsWith(
            "The SMT solver %s is not available on this machine because of missing libraries "
                .formatted(solverToUse()));
  }
}
