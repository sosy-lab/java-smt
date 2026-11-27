package org.sosy_lab.java_smt.basicimpl;

import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.common.rationals.Rational;

import java.util.Collection;
import java.util.Optional;

public abstract class AbstractOptimizationProver extends AbstractProver implements OptimizationProverEnvironment {
    
    protected final LogManager logger;
    protected final FormulaManager formulaManager;
    
    protected AbstractOptimizationProver(LogManager pLogger, FormulaManager pMgr) {
        this.logger = pLogger;
        this.formulaManager = pMgr;
    }
    
    @Override
    public boolean isOptimizationSupported() {
        return false; // Default implementation
    }
    
    @Override
    public int maximize(Formula objective) {
        if (!isOptimizationSupported()) {
            throw new UnsupportedOperationException(
                "Optimization not supported by " + getSolverName());
        }
        return maximizeInternal(objective);
    }
    
    @Override
    public int minimize(Formula objective) {
        if (!isOptimizationSupported()) {
            throw new UnsupportedOperationException(
                "Optimization not supported by " + getSolverName());
        }
        return minimizeInternal(objective);
    }
    
    protected abstract int maximizeInternal(Formula objective);
    protected abstract int minimizeInternal(Formula objective);
    protected abstract String getSolverName();
    
    @Override
    public Optional<Rational> upper(int handle, Rational epsilon) {
        if (!isOptimizationSupported()) {
            throw new UnsupportedOperationException(
                "Optimization not supported by " + getSolverName());
        }
        return upperInternal(handle, epsilon);
    }
    
    @Override
    public Optional<Rational> lower(int handle, Rational epsilon) {
        if (!isOptimizationSupported()) {
            throw new UnsupportedOperationException(
                "Optimization not supported by " + getSolverName());
        }
        return lowerInternal(handle, epsilon);
    }
    
    protected abstract Optional<Rational> upperInternal(int handle, Rational epsilon);
    protected abstract Optional<Rational> lowerInternal(int handle, Rational epsilon);
} 