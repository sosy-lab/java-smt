// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt_example;

import com.google.common.base.Joiner
import com.google.common.base.Splitter
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.params.Parameter
import org.junit.jupiter.params.ParameterizedClass
import org.junit.jupiter.params.provider.MethodSource
import org.sosy_lab.common.ShutdownNotifier
import org.sosy_lab.common.configuration.Configuration
import org.sosy_lab.common.log.BasicLogManager
import org.sosy_lab.common.log.LogManager
import org.sosy_lab.java_smt.SolverContextFactory
import org.sosy_lab.java_smt.SolverContextFactory.Solvers
import org.sosy_lab.java_smt.api.SolverContext
import org.sosy_lab.java_smt.example.Sudoku
import java.util.*
import kotlin.test.AfterTest
import kotlin.test.BeforeTest
import kotlin.test.Test

/**
 * This test parses a String-given Sudoku and solves it with an SMT solver.
 *
 *
 * This program is just an example and clearly SMT is not the best solution for solving Sudoku.
 * There might be other algorithms out there that are better suited for solving Sudoku.
 *
 *
 * The more numbers are available in a Sudoku, the easier it can be solved. A completely empty
 * Sudoku will cause the longest runtime in the solver, because it will guess a lot of values.
 *
 *
 * The Sudoku is read from a String and should be formatted as the following example:
 *
 * ```
 * 2..9.6..1
 * ..6.4...9
 * ...52.4..
 * 3.2..7.5.
 * ...2..1..
 * .9.3..7..
 * .87.5.31.
 * 6.3.1.8..
 * 4....9...
 * ```
 *
 * The solution will then be printed on StdOut and checked by an assertion, just like the
 * following solution:
 *
 * ```
 * 248976531
 * 536148279
 * 179523468
 * 312487956
 * 764295183
 * 895361742
 * 987652314
 * 623714895
 * 451839627
 * ```
 */

@ParameterizedClass
@MethodSource("getAllSolvers")
class AppTest {
    @Parameter(0)
    lateinit var solver: Solvers

    private lateinit var config: Configuration
    private lateinit var logger: LogManager
    private lateinit var notifier: ShutdownNotifier

    private lateinit var context: SolverContext

    @BeforeTest
    fun init() {
        config = Configuration.defaultConfiguration()
        logger = BasicLogManager.create(config)
        notifier = ShutdownNotifier.createDummy()
        context = SolverContextFactory.createSolverContext(config, logger, notifier, solver)
    }

    /* We close our context after we are done with a solver to not waste memory. */
    @AfterTest
    fun closeSolver() {
        context.close()
    }

    @Test
    fun checkSudoku() {
        assumeTrue(isOperatingSystemSupported(solver))

        val grid = readGridFromString(input)

        val sudoku = Sudoku.BooleanBasedSudokuSolver(context)
        val solution = sudoku.solve(grid)

        assertNotNull(solution)
        assertEquals(sudokuSolution, solutionToString(solution))
    }

    private fun solutionToString(solution: Array<Array<Int?>?>): String {
        val sb = StringBuilder()
        for (s1 in solution) {
            sb.append(Joiner.on("").join(s1!!)).append('\n')
        }
        return sb.toString().trim()
    }

    /**
     * A simple parser for a half-filled Sudoku.
     *
     *
     * Use digits 0-9 as values, other values will be set to 'unknown'.
     */
    private fun readGridFromString(puzzle: String): Array<Array<Int?>?> {
        val lines = Splitter.on('\n').splitToList(puzzle)
        val size = lines.size
        val grid = Array<Array<Int?>?>(size) { arrayOfNulls(size) }

        for (row in lines.indices) {
            for (col in 0..<lines.get(row).length) {
                val nextNumber = lines.get(row).get(col)
                if ('0' <= nextNumber && nextNumber <= '9') {
                    grid[row]!![col] = nextNumber.code - '0'.code
                }
            }
        }
        return grid
    }

    companion object {
        @JvmStatic
        fun getAllSolvers() = Solvers.entries.toTypedArray()

        private val OS = System.getProperty("os.name").lowercase(Locale.getDefault()).replace(" ", "")
        private val IS_LINUX = OS.startsWith("linux")
        private val IS_X64 = System.getProperty("os.arch").contains("64")

        /** Disable some checks on certain combinations of operating systems and solvers, because of missing dependencies.  */
        private fun isOperatingSystemSupported(solver: Solvers): Boolean {
            return when (solver) {
                Solvers.SMTINTERPOL, Solvers.PRINCESS -> true
                else -> IS_LINUX && IS_X64
            }
        }

        private val input = """
            |2..9.6..1
            |..6.4...9
            |...52.4..
            |3.2..7.5.
            |...2..1..
            |.9.3..7..
            |.87.5.31.
            |6.3.1.8..
            |4....9...
            """.trimMargin()

        private val sudokuSolution = """
            |248976531
            |536148279
            |179523468
            |312487956
            |764295183
            |895361742
            |987652314
            |623714895
            |451839627
            """.trimMargin()
    }
}
