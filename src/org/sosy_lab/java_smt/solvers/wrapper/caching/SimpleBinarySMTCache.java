/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.wrapper.caching;

import com.google.common.collect.ImmutableList;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;

public class SimpleBinarySMTCache implements SMTCache {

  private final static String CACHE_FILE = "java-smt.cache";

  private InMemorySMTCache cache;

  public SimpleBinarySMTCache() {
    cache = loadCacheFileIfExists();
  }

  private InMemorySMTCache loadCacheFileIfExists() {
    InMemorySMTCache newCache = new InMemorySMTCache();

    Path path = getCacheFilePath();
    File cacheFile = path.toFile();

    if (cacheFile.exists()) {
      try (ObjectInputStream os = new ObjectInputStream(new FileInputStream(cacheFile))) {
        newCache = (InMemorySMTCache) os.readObject();
      } catch (Exception e) {
        // TODO: handle exception
      }
    }

    return newCache;
  }

  private Path getCacheFilePath() {
    Path path = Paths.get("");
    path = Paths.get(path.toAbsolutePath().toString(), CACHE_FILE);
    return path;
  }

  @Override
  public Boolean storeFormulaUnsat(BooleanFormula pFormula, boolean pUnsat) {
    return cache.storeFormulaUnsat(pFormula, pUnsat);
  }

  @Override
  public Boolean isFormulaUnsat(BooleanFormula pFormula) {
    return cache.isFormulaUnsat(pFormula);
  }

  @Override
  public Boolean storeFormulaUnsatWithAssumptions(
      BooleanFormula pFormula,
      boolean pUnsat,
      Collection<BooleanFormula> pAssumptions) {
    return cache.storeFormulaUnsatWithAssumptions(pFormula, pUnsat, pAssumptions);
  }

  @Override
  public Boolean isFormulaUnsatWithAssumptions(
      BooleanFormula pFormula,
      Collection<BooleanFormula> pAssumptions) {
    return cache.isFormulaUnsatWithAssumptions(pFormula, pAssumptions);
  }

  @Override
  public Model storeFormulaModel(BooleanFormula pFormula, Model pModel) {
    return cache.storeFormulaModel(pFormula, pModel);
  }

  @Override
  public Model getFormulaModel(BooleanFormula pFormula) {
    return cache.getFormulaModel(pFormula);
  }

  @Override
  public ImmutableList<ValueAssignment> storeFormulaModelAssignments(
      BooleanFormula pFormula,
      ImmutableList<ValueAssignment> pAssignments) {
    return cache.storeFormulaModelAssignments(pFormula, pAssignments);
  }

  @Override
  public ImmutableList<ValueAssignment> getFormulaModelAssignments(BooleanFormula pFormula) {
    return cache.getFormulaModelAssignments(pFormula);
  }

  @Override
  public List<BooleanFormula>
      storeFormulaUnsatCore(BooleanFormula pFormula, List<BooleanFormula> pUnsatCore) {
    return cache.storeFormulaUnsatCore(pFormula, pUnsatCore);
  }

  @Override
  public List<BooleanFormula> getFormulaUnsatCore(BooleanFormula pFormula) {
    return cache.getFormulaUnsatCore(pFormula);
  }

  @Override
  public Optional<List<BooleanFormula>> storeFormulaUnsatCoreOverAssumptions(
      BooleanFormula pFormula,
      Optional<List<BooleanFormula>> pUnsatCore,
      Collection<BooleanFormula> pAssumptions) {
    return cache.storeFormulaUnsatCoreOverAssumptions(pFormula, pUnsatCore, pAssumptions);
  }

  @Override
  public Optional<List<BooleanFormula>> getFormulaUnsatCoreOverAssumptions(
      BooleanFormula pFormula,
      Collection<BooleanFormula> pAssumptions) {
    return cache.getFormulaUnsatCoreOverAssumptions(pFormula, pAssumptions);
  }

  @Override
  public BooleanFormula storeFormulaInterpolant(
      BooleanFormula pFormula,
      BooleanFormula pInterpolant,
      Collection<?> pFormulasOfA) {
    return cache.storeFormulaInterpolant(pFormula, pInterpolant, pFormulasOfA);
  }

  @Override
  public BooleanFormula getFormulaInterpolant(BooleanFormula pFormula, Collection<?> pFormulasOfA) {
    return cache.getFormulaInterpolant(pFormula, pFormulasOfA);
  }

  @Override
  public List<BooleanFormula> storeFormulaTreeInterpolants(
      BooleanFormula pFormula,
      List<BooleanFormula> pTreeInterpolants,
      List<? extends Collection<?>> pPartitionedFormulas,
      int[] pStartOfSubTree) {
    return cache.storeFormulaTreeInterpolants(
        pFormula,
        pTreeInterpolants,
        pPartitionedFormulas,
        pStartOfSubTree);
  }

  @Override
  public List<BooleanFormula> getFormulaTreeInterpolants(
      BooleanFormula pFormula,
      List<? extends Collection<?>> pPartitionedFormulas,
      int[] pStartOfSubTree) {
    return cache.getFormulaTreeInterpolants(pFormula, pPartitionedFormulas, pStartOfSubTree);
  }

  @Override
  public Integer storeFormulaMaximize(BooleanFormula pFormula, Integer pMax, Formula pObjective) {
    return cache.storeFormulaMaximize(pFormula, pMax, pObjective);
  }

  @Override
  public Integer getFormulaMaximize(BooleanFormula pFormula, Formula pObjective) {
    return cache.getFormulaMaximize(pFormula, pObjective);
  }

  @Override
  public Integer storeFormulaMinimize(BooleanFormula pFormula, Integer pMin, Formula pObjective) {
    return cache.storeFormulaMinimize(pFormula, pMin, pObjective);
  }

  @Override
  public Integer getFormulaMinimize(BooleanFormula pFormula, Formula pObjective) {
    return cache.getFormulaMinimize(pFormula, pObjective);
  }

  @Override
  public Optional<Rational> storeFormulaUpper(
      BooleanFormula pFormula,
      Optional<Rational> pUpper,
      int pHandle,
      Rational pEpsilon) {
    return cache.storeFormulaUpper(pFormula, pUpper, pHandle, pEpsilon);
  }

  @Override
  public Optional<Rational>
      getFormulaUpper(BooleanFormula pFormula, int pHandle, Rational pEpsilon) {
    return cache.getFormulaUpper(pFormula, pHandle, pEpsilon);
  }

  @Override
  public Optional<Rational> storeFormulaLower(
      BooleanFormula pFormula,
      Optional<Rational> pLower,
      int pHandle,
      Rational pEpsilon) {
    return cache.storeFormulaLower(pFormula, pLower, pHandle, pEpsilon);
  }

  @Override
  public Optional<Rational>
      getFormulaLower(BooleanFormula pFormula, int pHandle, Rational pEpsilon) {
    return cache.getFormulaLower(pFormula, pHandle, pEpsilon);
  }

  @Override
  public void close() {
    if (cache != null) {
      writeCacheFile(cache);
      cache = null;
    }
  }

  private void writeCacheFile(InMemorySMTCache pCache) {
    Path path = getCacheFilePath();
    File check = path.toFile();

    if (check.exists()) {
      check.delete();
    }

    try (ObjectOutputStream os = new ObjectOutputStream(new FileOutputStream(check))) {
      os.writeObject(pCache);
    } catch (Exception e) {
      // TODO: handle Exception
    }
  }
}