package org.sosy_lab.java-smt.src.org.sosy_lab.java_smt_solver_bdd;

public interface Region {

  /**
   * checks whether f represents "true"
   * @return true if f represents logical truth, false otherwise
   */
  boolean isTrue();

  /**
   * checks whether f represents "false"
   * @return true if f represents logical falsity, false otherwise
   */
  boolean isFalse();
}
