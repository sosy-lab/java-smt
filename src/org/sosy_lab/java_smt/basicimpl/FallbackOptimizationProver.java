package org.sosy_lab.java_smt.basicimpl;

import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.common.rationals.Rational;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.logging.Level;

/**
 * A fallback implementation of OptimizationProverEnvironment for solvers
 * that don't support optimization natively. This implementation uses
 * iterative solving to approximate optimization results.
 */
public class FallbackOptimizationProver extends AbstractOptimizationProver {
    private final BasicProverEnvironment baseProver;
    private final SolverContext context;
    private final Map<Integer, Formula> objectives;
    private int nextHandle;
    
    public FallbackOptimizationProver(
            SolverContext pContext,
            LogManager pLogger,
            FormulaManager pMgr,
            Set<SolverContext.ProverOptions> pOptions) {
        super(pLogger, pMgr);
        this.context = pContext;
        this.baseProver = pContext.newProverEnvironment(pOptions);
        this.objectives = new HashMap<>();
        this.nextHandle = 0;
    }
    
    @Override
    public boolean isOptimizationSupported() {
        return true; // We always support optimization through fallback
    }
    
    @Override
    protected String getSolverName() {
        return context.getSolverName();
    }
    
    @Override
    protected int maximizeInternal(Formula objective) {
        int handle = nextHandle++;
        objectives.put(handle, objective);
        return handle;
    }
    
    @Override
    protected int minimizeInternal(Formula objective) {
        // For minimization, we negate the objective and maximize
        FormulaManager fmgr = context.getFormulaManager();
        if (objective instanceof IntegerFormula) {
            IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();
            return maximizeInternal(imgr.negate((IntegerFormula) objective));
        } else if (objective instanceof RationalFormula) {
            // Handle rational formulas similarly
            // Implementation depends on the specific formula manager
            throw new UnsupportedOperationException(
                "Rational optimization not yet implemented in fallback");
        } else {
            throw new UnsupportedOperationException(
                "Unsupported formula type for optimization: " + objective.getClass());
        }
    }
    
    @Override
    protected Optional<Rational> upperInternal(int handle, Rational epsilon) {
        Formula objective = objectives.get(handle);
        if (objective == null) {
            throw new IllegalArgumentException("Invalid objective handle: " + handle);
        }
        
        try {
            // Start with a large upper bound
            Rational upperBound = Rational.ofLong(1000000);
            Rational lowerBound = Rational.ofLong(-1000000);
            
            // Binary search to find the maximum value
            while (upperBound.subtract(lowerBound).compareTo(epsilon) > 0) {
                Rational mid = upperBound.add(lowerBound).divide(Rational.ofLong(2));
                
                // Create constraint: objective <= mid
                BooleanFormula constraint = createUpperBoundConstraint(objective, mid);
                baseProver.push();
                baseProver.addConstraint(constraint);
                
                try {
                    if (baseProver.isUnsat()) {
                        // No solution exists with this upper bound
                        upperBound = mid;
                    } else {
                        // Solution exists, try a higher value
                        lowerBound = mid;
                    }
                } finally {
                    baseProver.pop();
                }
            }
            
            return Optional.of(upperBound);
        } catch (SolverException | InterruptedException e) {
            logger.log(Level.WARNING, "Error during optimization", e);
            return Optional.empty();
        }
    }
    
    @Override
    protected Optional<Rational> lowerInternal(int handle, Rational epsilon) {
        Formula objective = objectives.get(handle);
        if (objective == null) {
            throw new IllegalArgumentException("Invalid objective handle: " + handle);
        }
        
        try {
            // Start with a small lower bound
            Rational lowerBound = Rational.ofLong(-1000000);
            Rational upperBound = Rational.ofLong(1000000);
            
            // Binary search to find the minimum value
            while (upperBound.subtract(lowerBound).compareTo(epsilon) > 0) {
                Rational mid = upperBound.add(lowerBound).divide(Rational.ofLong(2));
                
                // Create constraint: objective >= mid
                BooleanFormula constraint = createLowerBoundConstraint(objective, mid);
                baseProver.push();
                baseProver.addConstraint(constraint);
                
                try {
                    if (baseProver.isUnsat()) {
                        // No solution exists with this lower bound
                        lowerBound = mid;
                    } else {
                        // Solution exists, try a lower value
                        upperBound = mid;
                    }
                } finally {
                    baseProver.pop();
                }
            }
            
            return Optional.of(lowerBound);
        } catch (SolverException | InterruptedException e) {
            logger.log(Level.WARNING, "Error during optimization", e);
            return Optional.empty();
        }
    }
    
    private BooleanFormula createUpperBoundConstraint(Formula objective, Rational bound) {
        FormulaManager fmgr = context.getFormulaManager();
        if (objective instanceof IntegerFormula) {
            IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();
            return imgr.lessOrEquals(
                (IntegerFormula) objective,
                imgr.makeNumber(bound.longValue()));
        } else if (objective instanceof RationalFormula) {
            // Handle rational formulas similarly
            // Implementation depends on the specific formula manager
            throw new UnsupportedOperationException(
                "Rational optimization not yet implemented in fallback");
        } else {
            throw new UnsupportedOperationException(
                "Unsupported formula type for optimization: " + objective.getClass());
        }
    }
    
    private BooleanFormula createLowerBoundConstraint(Formula objective, Rational bound) {
        FormulaManager fmgr = context.getFormulaManager();
        if (objective instanceof IntegerFormula) {
            IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();
            return imgr.greaterOrEquals(
                (IntegerFormula) objective,
                imgr.makeNumber(bound.longValue()));
        } else if (objective instanceof RationalFormula) {
            // Handle rational formulas similarly
            // Implementation depends on the specific formula manager
            throw new UnsupportedOperationException(
                "Rational optimization not yet implemented in fallback");
        } else {
            throw new UnsupportedOperationException(
                "Unsupported formula type for optimization: " + objective.getClass());
        }
    }
    
    @Override
    public void close() {
        baseProver.close();
    }
} 