// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt_web_example;

import com.google.common.base.StandardSystemProperty;
import java.util.Locale;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.SolverContextFactory;

class Platform {
  private static final String OS =
          StandardSystemProperty.OS_NAME.value().toLowerCase(Locale.getDefault()).replace(" ", "");
  private static final String ARCH =
          StandardSystemProperty.OS_ARCH.value().toLowerCase(Locale.getDefault()).replace(" ", "");

  private static final boolean IS_WINDOWS = OS.startsWith("windows");
  private static final boolean IS_MAC = OS.startsWith("macos");
  private static final boolean IS_LINUX = OS.startsWith("linux");

  private static final boolean IS_ARCH_ARM64 = ARCH.equals("aarch64");

  private static boolean isSufficientVersionOfLibcxx(String library) {
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

  private static String[] getRequiredLibcxx(String library) {
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

  /**
   * <code>True</code> if the solver is supported on the current operating system and CPU
   * architecture
   */
  static boolean isSupported(SolverContextFactory.Solvers solver) {
    return switch (solver) {
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
      case Z3_WITH_INTERPOLATION -> IS_LINUX && !IS_ARCH_ARM64;
    };
  }
}
