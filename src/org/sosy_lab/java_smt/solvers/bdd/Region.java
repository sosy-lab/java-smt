package org.sosy_lab.java_smt.solvers.bdd;

public interface Region {
  boolean isTrue();
  boolean isFalse();
}