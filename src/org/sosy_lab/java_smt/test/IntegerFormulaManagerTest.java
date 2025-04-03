package org.sosy_lab.java_smt.test;
import java.math.BigDecimal;
import org.junit.Test;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;

public class IntegerFormulaManagerTest extends SolverBasedTest0 {

  @Test
  public void testBigDecimalInIntegerFormula() throws SolverException, InterruptedException {
    // Test that BigDecimal values are handled correctly by all solvers
    IntegerFormula f = imgr.makeNumber(BigDecimal.valueOf(3.5));
    IntegerFormula three = imgr.makeNumber(3);
    BooleanFormula equals = bmgr.equal(f, three);
    assertThatFormula(equals).isSatisfiable();
  }
  
  @Test
  public void testEuclideanDivisionForNegativeValues() throws SolverException, InterruptedException {
    requireIntegers();
    
    // Test euclidean division for negative values with fractional parts
    // For -3.5, we expect -4 (not -3 that simple truncation would give)
    IntegerFormula f = imgr.makeNumber(BigDecimal.valueOf(-3.5));
    IntegerFormula minusFour = imgr.makeNumber(-4);
    
    // This should be a tautology if euclidean division is working correctly
    assertThatFormula(imgr.equal(f, minusFour)).isTautological();
  }
}
