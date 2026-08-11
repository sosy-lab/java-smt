// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0
package org.sosy_lab.java_smt_example

import com.google.common.base.StandardSystemProperty
import org.sosy_lab.common.NativeLibraries
import org.sosy_lab.java_smt.SolverContextFactory
import java.util.*

internal object Platform {
    private val OS: String = StandardSystemProperty.OS_NAME.value()!!.lowercase(Locale.getDefault()).replace(" ", "")
    private val ARCH: String = StandardSystemProperty.OS_ARCH.value()!!.lowercase(Locale.getDefault()).replace(" ", "")

    private val IS_WINDOWS: Boolean = OS.startsWith("windows")
    private val IS_MAC: Boolean = OS.startsWith("macos")
    private val IS_LINUX: Boolean = OS.startsWith("linux")

    private val IS_ARCH_ARM64: Boolean = ARCH.equals("aarch64")

    private fun isSufficientVersionOfLibcxx(library: String): Boolean {
        try {
            NativeLibraries.loadLibrary(library)
        } catch (e: UnsatisfiedLinkError) {
            for (dependency in getRequiredLibcxx(library)) {
                if (e.message!!.contains("version `" + dependency + "' not found")) {
                    return false
                }
            }
        }
        return true
    }

    private fun getRequiredLibcxx(library: String): Array<out String?> {
        return when (library) {
            "z3" -> arrayOf<String>("GLIBC_2.34", "GLIBCXX_3.4.26", "GLIBCXX_3.4.29")
            "bitwuzlaj" -> arrayOf<String>("GLIBC_2.33", "GLIBCXX_3.4.26", "GLIBCXX_3.4.29")
            "opensmtj" -> arrayOf<String>("GLIBC_2.33", "GLIBCXX_3.4.26", "GLIBCXX_3.4.29")
            "mathsat5j" -> arrayOf<String>("GLIBC_2.33", "GLIBC_2.38")
            "cvc5jni" -> arrayOf<String>("GLIBC_2.32")
            "yices2java" -> arrayOf<String>("GLIBC_2.34")
            else -> arrayOf<String?>()
        }
    }

    /**
     * `True` if the solver is supported on the current operating system and CPU
     * architecture
     */
    fun isSupported(solver: SolverContextFactory.Solvers): Boolean {
        return when (solver) {
            SolverContextFactory.Solvers.SMTINTERPOL, SolverContextFactory.Solvers.PRINCESS ->
                // Any operating system and any architecture is allowed, Java is sufficient
                true

            SolverContextFactory.Solvers.BOOLECTOR, SolverContextFactory.Solvers.CVC4 ->
                IS_LINUX && !IS_ARCH_ARM64

            SolverContextFactory.Solvers.YICES2 ->
                (IS_LINUX && !IS_ARCH_ARM64 && isSufficientVersionOfLibcxx("yices2java")) || (IS_WINDOWS && !IS_ARCH_ARM64)

            SolverContextFactory.Solvers.CVC5 ->
                (IS_LINUX && isSufficientVersionOfLibcxx("cvc5jni")) || IS_WINDOWS || IS_MAC

            SolverContextFactory.Solvers.OPENSMT ->
                IS_LINUX && isSufficientVersionOfLibcxx("opensmtj")

            SolverContextFactory.Solvers.BITWUZLA ->
                (IS_LINUX && isSufficientVersionOfLibcxx("bitwuzlaj")) || (IS_WINDOWS && !IS_ARCH_ARM64)

            SolverContextFactory.Solvers.MATHSAT5 ->
                (IS_LINUX && isSufficientVersionOfLibcxx("mathsat5j")) || (IS_WINDOWS && !IS_ARCH_ARM64)

            SolverContextFactory.Solvers.Z3 ->
                (IS_LINUX && isSufficientVersionOfLibcxx("z3")) || IS_WINDOWS || IS_MAC

            SolverContextFactory.Solvers.Z3_WITH_INTERPOLATION ->
                IS_LINUX && !IS_ARCH_ARM64
        }
    }
}