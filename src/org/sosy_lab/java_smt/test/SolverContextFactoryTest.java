// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assert_;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.base.StandardSystemProperty;
import com.google.common.truth.StandardSubjectBuilder;
import java.util.Locale;
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

/**
 * This JUnit test class is mainly intended for automated CI checks on different operating systems,
 * where a plain environment without pre-installed solvers is guaranteed.
 */
@RunWith(Parameterized.class)
public class SolverContextFactoryTest {
  @Before
  public void checkNotSolverless() {
    assume().that(solverToUse()).isNotEqualTo(Solvers.SOLVERLESS);
  }

  private static final String OS =
      StandardSystemProperty.OS_NAME.value().toLowerCase(Locale.getDefault()).replace(" ", "");
  private static final boolean IS_WINDOWS = OS.startsWith("windows");
  private static final boolean IS_MAC = OS.startsWith("macos");
  private static final boolean IS_LINUX = OS.startsWith("linux");

  protected Configuration config;
  protected final LogManager logger = LogManager.createTestLogManager();
  protected ShutdownManager shutdownManager = ShutdownManager.create();

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
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
  private void requireSupportedOperatingSystem() {
    StandardSubjectBuilder assume =
        assume()
            .withMessage(
                "Solver %s is not yet supported in the operating system %s", solverToUse(), OS);
    switch (solverToUse()) {
      case SMTINTERPOL:
      case PRINCESS:
        // any operating system is allowed, Java is already available.
        return;
      case BOOLECTOR:
      case CVC4:
      case CVC5:
      case OPENSMT:
      case YICES2:
        assume.that(IS_LINUX).isTrue();
        return;
      case MATHSAT5:
        assume.that(IS_LINUX || IS_WINDOWS).isTrue();
        return;
      case Z3:
        assume.that(IS_LINUX || IS_WINDOWS || IS_MAC).isTrue();
        return;
      default:
        throw new AssertionError("unexpected solver: " + solverToUse());
    }
  }

  @Before
  public final void initSolver() throws InvalidConfigurationException {
    config = Configuration.builder().setOption("solver.solver", solverToUse().toString()).build();
  }

  @Test
  public void createSolverContextFactoryWithDefaultLoader() throws InvalidConfigurationException {
    requireSupportedOperatingSystem();

    SolverContextFactory factory =
        new SolverContextFactory(config, logger, shutdownManager.getNotifier());
    try (SolverContext context = factory.generateContext()) {
      @SuppressWarnings("unused")
      FormulaManager mgr = context.getFormulaManager();
    }
  }

  @Test
  public void createSolverContextFactoryWithSystemLoader() throws InvalidConfigurationException {
    requireNativeLibrary();
    requireSupportedOperatingSystem();

    // we assume that no native solvers are installed on the testing machine by default.
    SolverContextFactory factory =
        new SolverContextFactory(
            config, logger, shutdownManager.getNotifier(), System::loadLibrary);
    try (SolverContext context = factory.generateContext()) {
      assert_().fail();
      @SuppressWarnings("unused")
      FormulaManager mgr = context.getFormulaManager();
    } catch (InvalidConfigurationException e) {
      assert_().that(e).hasCauseThat().isInstanceOf(UnsatisfiedLinkError.class);
    }
  }

  @Test
  public void createSolverContextFactoryWithSystemLoaderForJavaSolver()
      throws InvalidConfigurationException {
    requireNoNativeLibrary();
    requireSupportedOperatingSystem();

    SolverContextFactory factory =
        new SolverContextFactory(
            config, logger, shutdownManager.getNotifier(), System::loadLibrary);
    try (SolverContext context = factory.generateContext()) {
      @SuppressWarnings("unused")
      FormulaManager mgr = context.getFormulaManager();
    }
  }
}
