package org.sosy_lab.solver.test;

import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.solver.api.InterpolatingProverEnvironment;
import org.sosy_lab.solver.api.InterpolatingProverEnvironmentWithAssumptions;
import org.sosy_lab.solver.basicimpl.InterpolatingProverWithAssumptionsWrapper;

public class InterpolatingProverWithAssumptionsWrapperTest
    extends SolverFormulaWithAssumptionsTest {

  @Override
  @SuppressWarnings({"unchecked", "rawtypes"})
  protected <T> InterpolatingProverEnvironmentWithAssumptions<T> newEnvironmentForTest()
      throws InvalidConfigurationException {
    final InterpolatingProverEnvironment<?> proverEnvironment =
        context.newProverEnvironmentWithInterpolation();
    return new InterpolatingProverWithAssumptionsWrapper(proverEnvironment, mgr);
  }
}
