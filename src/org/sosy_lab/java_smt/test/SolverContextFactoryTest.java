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
import static org.junit.jupiter.api.Assertions.assertThrows;

import com.google.common.base.StandardSystemProperty;
import java.util.Locale;
import java.util.regex.Pattern;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.Parameter;
import org.junit.jupiter.params.ParameterizedClass;
import org.junit.jupiter.params.provider.MethodSource;
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
@ParameterizedClass
@MethodSource("getAllSolvers")
public class SolverContextFactoryTest {

  private static final String OS =
      StandardSystemProperty.OS_NAME.value().toLowerCase(Locale.getDefault()).replace(" ", "");
  private static final String ARCH =
      StandardSystemProperty.OS_ARCH.value().toLowerCase(Locale.getDefault()).replace(" ", "");

  protected static final boolean IS_WINDOWS = OS.startsWith("windows");
  private static final boolean IS_MAC = OS.startsWith("macos");
  private static final boolean IS_LINUX = OS.startsWith("linux");

  private static final boolean IS_ARCH_ARM64 = ARCH.equals("aarch64");

  protected Configuration config;
  protected final LogManager logger = LogManager.createTestLogManager();
  protected ShutdownManager shutdownManager = ShutdownManager.create();

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
        .withMessage(
            "Solver %s is not yet supported in the operating system %s with architecture %s",
            solverToUse(), OS, ARCH)
        .that(isSupportedOperatingSystemAndArchitecture())
        .isTrue();
  }

  private void requirePlatformNotSupported() {
    assume()
        .withMessage(
            "Solver %s is not yet supported in the operating system %s with architecture %s",
            solverToUse(), OS, ARCH)
        .that(isSupportedOperatingSystemAndArchitecture())
        .isFalse();
  }

  /**
   * This method represents the matrix of supported operating systems and architectures, which can
   * be tested in our CI. It might be possible that JavaSMT runs on more systems than listed here,
   * but we do not explicitly test them in our CI.
   */
  private boolean isSupportedOperatingSystemAndArchitecture() {
    return switch (solverToUse()) {
      case SMTINTERPOL, PRINCESS ->
          // Any operating system and any architecture is allowed, Java is sufficient
          true;
      case BOOLECTOR, CVC4 -> IS_LINUX && !IS_ARCH_ARM64;
      case YICES2 ->
          (IS_LINUX && !IS_ARCH_ARM64 && isSufficientVersionOfLibcxx("yices2java"))
              || (IS_WINDOWS && !IS_ARCH_ARM64);
      case CVC5 -> (IS_LINUX && isSufficientVersionOfLibcxx("cvc5jni")) || IS_WINDOWS || IS_MAC;
      case OPENSMT -> IS_LINUX && isSufficientVersionOfLibcxx("opensmtj");
      case BITWUZLA ->
          (IS_LINUX && isSufficientVersionOfLibcxx("bitwuzlaj")) || (IS_WINDOWS && !IS_ARCH_ARM64);
      case MATHSAT5 ->
          (IS_LINUX && isSufficientVersionOfLibcxx("mathsat5j")) || (IS_WINDOWS && !IS_ARCH_ARM64);
      case Z3 -> (IS_LINUX && isSufficientVersionOfLibcxx("z3")) || IS_WINDOWS || IS_MAC;
      case Z3_WITH_INTERPOLATION -> IS_LINUX;
    };
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
    return switch (library) {
      case "z3" -> new String[] {"GLIBC_2.34", "GLIBCXX_3.4.26", "GLIBCXX_3.4.29"};
      case "bitwuzlaj" -> new String[] {"GLIBC_2.33", "GLIBCXX_3.4.26", "GLIBCXX_3.4.29"};
      case "opensmtj" -> new String[] {"GLIBC_2.33", "GLIBCXX_3.4.26", "GLIBCXX_3.4.29"};
      case "mathsat5j" -> new String[] {"GLIBC_2.33", "GLIBC_2.38"};
      case "cvc5jni" -> new String[] {"GLIBC_2.32"};
      case "yices2java" -> new String[] {"GLIBC_2.34"};
      default -> new String[] {};
    };
  }

  @BeforeEach
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
            InvalidConfigurationException.class,
            factory::generateContext,
            "Expected InvalidConfigurationException due to failure in loading native library");
    assert_().that(thrown).hasCauseThat().isInstanceOf(UnsatisfiedLinkError.class);
    assert_()
        .that(thrown)
        .hasMessageThat()
        .startsWith(
            "The SMT solver %s is not available on this machine because of missing libraries "
                .formatted(solverToUse()));
  }
}
