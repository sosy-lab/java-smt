
package org.sosy_lab.java_smt.solvers.bdd;

import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;

public class BddFormulaManager {

  private final RegionManager rmgr;

  public BddFormulaManager(Configuration config, LogManager logger)
      throws InvalidConfigurationException {
    BDDManagerFactory factory = new BDDManagerFactory(config, logger);
    rmgr = factory.createRegionManager();


  }

}
