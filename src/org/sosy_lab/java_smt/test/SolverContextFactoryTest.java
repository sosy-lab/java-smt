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
import static org.junit.Assert.assertThrows;

import com.google.common.base.StandardSystemProperty;
import com.google.common.truth.StandardSubjectBuilder;
import java.util.Locale;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.NativeLibraries;
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

  private static final String OS =
      StandardSystemProperty.OS_NAME.value().toLowerCase(Locale.getDefault()).replace(" ", "");
  protected static final boolean IS_WINDOWS = OS.startsWith("windows");
  private static final boolean IS_MAC = OS.startsWith("macos");
  private static final boolean IS_LINUX = OS.startsWith("linux");

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
      case YICES2:
        assume.that(IS_LINUX).isTrue();
        return;
      case CVC5:
        assume.that(IS_LINUX || IS_WINDOWS).isTrue();
        if (IS_LINUX) {
          assume.that(isSufficientVersionOfLibcxx("cvc5")).isTrue();
        }
        return;
      case OPENSMT:
        assume.that(IS_LINUX).isTrue();
        assume.that(isSufficientVersionOfLibcxx("opensmtj")).isTrue();
        return;
      case BITWUZLA:
        assume.that(IS_LINUX).isTrue();
        assume.that(isSufficientVersionOfLibcxx("bitwuzlaj")).isTrue();
        return;
      case MATHSAT5:
        assume.that(IS_LINUX || IS_WINDOWS).isTrue();
        if (IS_LINUX) {
          assume.that(isSufficientVersionOfLibcxx("mathsat5j")).isTrue();
        }
        return;
      case Z3:
        assume.that(IS_LINUX || IS_WINDOWS || IS_MAC).isTrue();
        if (IS_LINUX) {
          assume.that(isSufficientVersionOfLibcxx("z3")).isTrue();
        }
        return;
      default:
        throw new AssertionError("unexpected solver: " + solverToUse());
    }
  }

  /**
   * Some libraries require GLIBC in version 2.34 or GLIBCXX in version 3.4.26 or newer. This
   * excludes Ubuntu 18.04 or 20.04 for some solvers.
   */
  private boolean isSufficientVersionOfLibcxx(String library) {
    try {
      NativeLibraries.loadLibrary(library);
    } catch (UnsatisfiedLinkError e) {
      for (String dependency : getRequiredLibcxx(library)) {
        if (e.getMessage().contains("version `" + dependency + "' not found")) {
          return false;
        }
      }
    }
    return true;
  }

  private String[] getRequiredLibcxx(String library) {
    switch (library) {
      case "z3":
        return new String[] {"GLIBC_2.34", "GLIBCXX_3.4.26", "GLIBCXX_3.4.29"};
      case "bitwuzlaj":
        return new String[] {"GLIBCXX_3.4.26", "GLIBCXX_3.4.29"};
      case "opensmtj":
        return new String[] {"GLIBC_2.33", "GLIBCXX_3.4.26", "GLIBCXX_3.4.29"};
      case "mathsat5j":
        return new String[] {"GLIBC_2.33"};
      case "cvc5":
        return new String[] {"GLIBC_2.32"};
      default:
        return new String[] {};
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
    assert_()
        .that(assertThrows(InvalidConfigurationException.class, () -> factory.generateContext()))
        .hasCauseThat()
        .isInstanceOf(UnsatisfiedLinkError.class);
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
