
package org.sosy_lab.java_smt.solvers.bdd;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;


public class BddContext {
  public static void main(String[] args) {

    // TODO BddContext
    BiMap<String, Region> biMap = HashBiMap.create();
    String param1 = null;
    Region param2 = null;

    biMap.put(param1, param2);

    System.out.println("param1=" + biMap.get("param1"));
    System.out.println("param2=" + biMap.get("param2"));

  }
}

