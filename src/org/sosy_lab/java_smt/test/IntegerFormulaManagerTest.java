package org.sosy_lab.java_smt.test;
import java.math.BigDecimal;
import org.junit.Test;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;

public class IntegerFormulaManagerTest extends SolverBasedTest0 {

  @Test
  public void testBigDecimalInIntegerFormula() throws SolverException, InterruptedException {
    // Test that BigDecimal values are handled correctly by all solvers
    IntegerFormula f = imgr.makeNumber(BigDecimal.valueOf(3.5));
    IntegerFormula three = imgr.makeNumber(3);
    BooleanFormula equals = bmgr.equals(f, three);
    assertThatFormula(equals).isSatisfiable();
  }
}
