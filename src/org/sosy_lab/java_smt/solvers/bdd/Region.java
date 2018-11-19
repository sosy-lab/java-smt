package org.sosy_lab.cpachecker.util.predicates.regions;

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
