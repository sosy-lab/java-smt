package org.sosy_lab.java_smt.solvers.cvc4;

import edu.nyu.acsys.CVC4.CVC4JNI;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Type;
import java.util.Set;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public final class CVC4SolverContext extends AbstractSolverContext {
  private final CVC4FormulaManager manager;
  private final CVC4FormulaCreator creator;

  private CVC4SolverContext(CVC4FormulaCreator creator, CVC4FormulaManager manager) {
    super(manager);
    this.creator = creator;
    this.manager = manager;
  }

  public static SolverContext create(int randomSeed, NonLinearArithmetic pNonLinearArithmetic) {

    // Init CVC4
    NativeLibraries.loadLibrary("cvc4jni");
    ExprManager exprManager = new ExprManager();
    Type boolType = exprManager.booleanType();
    Type intType = exprManager.integerType();
    Type realType = exprManager.realType();

    // Create CVC4FormulaCreator
    CVC4FormulaCreator creator =
        new CVC4FormulaCreator(randomSeed, exprManager, boolType, intType, realType);

    // Create managers
    CVC4UFManager functionTheory = new CVC4UFManager(creator);
    CVC4BooleanFormulaManager booleanTheory = new CVC4BooleanFormulaManager(creator);
    CVC4IntegerFormulaManager integerTheory =
        new CVC4IntegerFormulaManager(creator, pNonLinearArithmetic);
    CVC4RationalFormulaManager rationalTheory =
        new CVC4RationalFormulaManager(creator, pNonLinearArithmetic);
    CVC4BitvectorFormulaManager bitvectorTheory = new CVC4BitvectorFormulaManager(creator);
    CVC4ArrayFormulaManager arrayTheory = new CVC4ArrayFormulaManager(creator);
    CVC4FormulaManager manager =
        new CVC4FormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory,
            arrayTheory);

    return new CVC4SolverContext(creator, manager);
  }

  public FormulaManager getFormulaManager0() {
    return manager;
  }

  @Override
  public String getVersion() {
    return "CVC4 " + CVC4JNI.Configuration_getVersionString();
  }

  @Override
  public void close() {
    // TODO: closing context.
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.CVC4;
  }

  @Override
  public ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    return new CVC4TheoremProver(creator, manager);
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    // TODO Auto-generated method stub
    return false;
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pSet) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    // TODO Auto-generated method stub
    throw new UnsupportedOperationException();
  }
}
