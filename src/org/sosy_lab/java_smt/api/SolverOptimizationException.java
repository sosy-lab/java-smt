package org.sosy_lab.java_smt.api;

/**
 * Exception thrown when a solver does not support optimization features
 * or when there are version-specific optimization issues.
 */
public class SolverOptimizationException extends SolverException {
    private static final long serialVersionUID = 1L;
    private final String solverName;
    private final String feature;
    
    public SolverOptimizationException(String solverName, String feature) {
        super(String.format("%s does not support %s", solverName, feature));
        this.solverName = solverName;
        this.feature = feature;
    }
    
    public SolverOptimizationException(String solverName, String feature, String reason) {
        super(String.format("%s does not support %s: %s", solverName, feature, reason));
        this.solverName = solverName;
        this.feature = feature;
    }
    
    public String getSolverName() {
        return solverName;
    }
    
    public String getFeature() {
        return feature;
    }
} 