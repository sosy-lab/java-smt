
package org.sosy_lab.java_smt.solvers.bdd;

import com.microsoft.z3.FuncDecl;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

public class BddFormulaManager
    extends AbstractFormulaManager<Region, BddSort, NamedRegionManager, FuncDecl> {

  public BddFormulaManager(
      BddFormulaCreator creator,
      BddBooleanFormulaManager booleanMgr) {
    super(creator, null, booleanMgr, null, null, null, null, null, null);
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Appender dumpFormula(Region pT) {
    // TODO Auto-generated method stub
    return null;
  }


}
