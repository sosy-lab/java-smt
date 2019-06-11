package org.sosy_lab.java_smt.solvers.cvc4;

import edu.nyu.acsys.CVC4.CVC4JNI;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.SmtEngine;
import java.util.Set;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public final class CVC4SolverContext extends AbstractSolverContext {
  private final CVC4FormulaCreator creator;

  private CVC4SolverContext(CVC4FormulaCreator creator, CVC4FormulaManager manager) {
    super(manager);
    this.creator = creator;
  }

  public static SolverContext create(
      int randomSeed,
      NonLinearArithmetic pNonLinearArithmetic,
      ShutdownNotifier pShutdownNotifier) {

    // Init CVC4
    NativeLibraries.loadLibrary("cvc4jni");
    ExprManager exprManager = new ExprManager();
    SmtEngine smt = new SmtEngine(exprManager);
    smt.setLogic("QF_ALL_SUPPORTED");

    CVC4Environment env = new CVC4Environment(exprManager, randomSeed, pShutdownNotifier, false);

    // Create CVC4FormulaCreator
    CVC4FormulaCreator creator = new CVC4FormulaCreator(env);

    // Create managers
    CVC4UFManager functionTheory = new CVC4UFManager(creator);
    CVC4BooleanFormulaManager booleanTheory = new CVC4BooleanFormulaManager(creator);
    CVC4IntegerFormulaManager integerTheory =
        new CVC4IntegerFormulaManager(creator, pNonLinearArithmetic);
    CVC4RationalFormulaManager rationalTheory =
        new CVC4RationalFormulaManager(creator, pNonLinearArithmetic);
    CVC4BitvectorFormulaManager bitvectorTheory = new CVC4BitvectorFormulaManager(creator);
    CVC4ArrayFormulaManager arrayTheory = new CVC4ArrayFormulaManager(creator);
    CVC4SLFormulaManager slTheory = new CVC4SLFormulaManager(creator);
    CVC4FormulaManager manager =
        new CVC4FormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory,
            arrayTheory,
            slTheory);

    return new CVC4SolverContext(creator, manager);
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
    return new CVC4TheoremProver(creator);
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
