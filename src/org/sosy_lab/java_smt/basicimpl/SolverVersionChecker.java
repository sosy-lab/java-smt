package org.sosy_lab.java_smt.basicimpl;

import org.sosy_lab.java_smt.api.SolverOptimizationException;
import org.sosy_lab.java_smt.api.Solvers;

/**
 * Utility class for checking solver versions and compatibility.
 */
public final class SolverVersionChecker {
    private SolverVersionChecker() {}
    
    /**
     * Check if the given MathSAT5 version has known optimization bugs.
     * @param version The solver version string
     * @throws SolverOptimizationException if the version has known issues
     */
    public static void checkMathSATVersion(String version) {
        if (version.startsWith("1.7.2") || version.startsWith("1.7.3")) {
            throw new SolverOptimizationException(
                Solvers.MATHSAT5.name(),
                "optimization",
                "version " + version + " has known optimization bugs");
        }
    }
    
    /**
     * Check if optimization is supported for the given solver.
     * @param solver The solver to check
     * @return true if optimization is supported
     */
    public static boolean isOptimizationSupported(Solvers solver) {
        return solver == Solvers.Z3 || solver == Solvers.MATHSAT5;
    }
    
    /**
     * Get a descriptive message about optimization support for a solver.
     * @param solver The solver to check
     * @return A message describing optimization support
     */
    public static String getOptimizationSupportMessage(Solvers solver) {
        if (solver == Solvers.Z3) {
            return "Z3 provides full optimization support";
        } else if (solver == Solvers.MATHSAT5) {
            return "MathSAT5 provides partial optimization support (versions > 1.7.3)";
        } else {
            return solver.name() + " does not support optimization";
        }
    }
} 