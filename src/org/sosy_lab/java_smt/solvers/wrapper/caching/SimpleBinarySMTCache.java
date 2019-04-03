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
import com.google.common.io.MoreFiles;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;

@Options(prefix = "solver.caching")
public class SimpleBinarySMTCache implements SMTCache {

  @Option(
      secure = true,
      description = "Cache SMT-Solver results to this file on disc.",
      name = "file")
  @FileOption(FileOption.Type.OUTPUT_FILE)
  private Path fileName = Paths.get("java-smt.cache");

  @Option(
      secure = true,
      description = "Read cached SMT-Solver results from this file on disc",
      name = "input")
  @FileOption(FileOption.Type.OPTIONAL_INPUT_FILE)
  private Path inputFileName = Paths.get("output/java-smt.cache");

  private Path tempFileLocation;

  private InMemorySMTCache cache;

  public SimpleBinarySMTCache(Configuration config) throws InvalidConfigurationException {
    config.inject(this);
    tempFileLocation = fileName != null ? Paths.get(fileName.toString() + ".tmp") : null;
    cache = loadCacheFileIfExists();
    deleteTempFileIfExists();
  }

  private void deleteTempFileIfExists() {
    try {
      Files.deleteIfExists(tempFileLocation);
    } catch (IOException e) {
      throw new RuntimeException("Old temporary cache-file could not be deleted.", e);
    }
  }

  private InMemorySMTCache loadCacheFileIfExists() {
    InMemorySMTCache newCache = new InMemorySMTCache();

    if (inputFileName != null && Files.exists(inputFileName) && Files.isReadable(inputFileName)) {
      createParentDirectoryIfNecessary(inputFileName);
      try (ObjectInputStream os = new ObjectInputStream(Files.newInputStream(inputFileName))) {
        newCache = (InMemorySMTCache) os.readObject();
      } catch (Exception e) {
        throw new RuntimeException("Could not load SMT-cachefile from disc.", e);
      }
    }

    return newCache;
  }

  @Override
  public Boolean storeFormulaUnsat(Formula pFormula, boolean pUnsat) {
    return cache.storeFormulaUnsat(pFormula, pUnsat);
  }

  @Override
  public Boolean isFormulaUnsat(Formula pFormula) {
    return cache.isFormulaUnsat(pFormula);
  }

  @Override
  public Boolean storeFormulaUnsatWithAssumptions(
      Formula pFormula, boolean pUnsat, Collection<Formula> pAssumptions) {
    return cache.storeFormulaUnsatWithAssumptions(pFormula, pUnsat, pAssumptions);
  }

  @Override
  public Boolean isFormulaUnsatWithAssumptions(Formula pFormula, Collection<Formula> pAssumptions) {
    return cache.isFormulaUnsatWithAssumptions(pFormula, pAssumptions);
  }

  @Override
  public Model storeFormulaModel(Formula pFormula, Model pModel) {
    return cache.storeFormulaModel(pFormula, pModel);
  }

  @Override
  public Model getFormulaModel(Formula pFormula) {
    return cache.getFormulaModel(pFormula);
  }

  @Override
  public ImmutableList<ValueAssignment> storeFormulaModelAssignments(
      Formula pFormula, ImmutableList<ValueAssignment> pAssignments) {
    return cache.storeFormulaModelAssignments(pFormula, pAssignments);
  }

  @Override
  public ImmutableList<ValueAssignment> getFormulaModelAssignments(Formula pFormula) {
    return cache.getFormulaModelAssignments(pFormula);
  }

  @Override
  public List<Formula> storeFormulaUnsatCore(Formula pFormula, List<Formula> pUnsatCore) {
    return cache.storeFormulaUnsatCore(pFormula, pUnsatCore);
  }

  @Override
  public List<Formula> getFormulaUnsatCore(Formula pFormula) {
    return cache.getFormulaUnsatCore(pFormula);
  }

  @Override
  public Optional<List<Formula>> storeFormulaUnsatCoreOverAssumptions(
      Formula pFormula, Optional<List<Formula>> pUnsatCore, Collection<Formula> pAssumptions) {
    return cache.storeFormulaUnsatCoreOverAssumptions(pFormula, pUnsatCore, pAssumptions);
  }

  @Override
  public Optional<List<Formula>> getFormulaUnsatCoreOverAssumptions(
      Formula pFormula, Collection<Formula> pAssumptions) {
    return cache.getFormulaUnsatCoreOverAssumptions(pFormula, pAssumptions);
  }

  @Override
  public Formula storeFormulaInterpolant(
      Formula pFormula, Formula pInterpolant, Collection<?> pFormulasOfA) {
    return cache.storeFormulaInterpolant(pFormula, pInterpolant, pFormulasOfA);
  }

  @Override
  public Formula getFormulaInterpolant(Formula pFormula, Collection<?> pFormulasOfA) {
    return cache.getFormulaInterpolant(pFormula, pFormulasOfA);
  }

  @Override
  public List<Formula> storeFormulaTreeInterpolants(
      Formula pFormula,
      List<Formula> pTreeInterpolants,
      List<? extends Collection<?>> pPartitionedFormulas,
      int[] pStartOfSubTree) {
    return cache.storeFormulaTreeInterpolants(
        pFormula, pTreeInterpolants, pPartitionedFormulas, pStartOfSubTree);
  }

  @Override
  public List<Formula> getFormulaTreeInterpolants(
      Formula pFormula, List<? extends Collection<?>> pPartitionedFormulas, int[] pStartOfSubTree) {
    return cache.getFormulaTreeInterpolants(pFormula, pPartitionedFormulas, pStartOfSubTree);
  }

  @Override
  public Integer storeFormulaMaximize(Formula pFormula, Integer pMax, Formula pObjective) {
    return cache.storeFormulaMaximize(pFormula, pMax, pObjective);
  }

  @Override
  public Integer getFormulaMaximize(Formula pFormula, Formula pObjective) {
    return cache.getFormulaMaximize(pFormula, pObjective);
  }

  @Override
  public Integer storeFormulaMinimize(Formula pFormula, Integer pMin, Formula pObjective) {
    return cache.storeFormulaMinimize(pFormula, pMin, pObjective);
  }

  @Override
  public Integer getFormulaMinimize(Formula pFormula, Formula pObjective) {
    return cache.getFormulaMinimize(pFormula, pObjective);
  }

  @Override
  public Optional<Rational> storeFormulaUpper(
      Formula pFormula, Optional<Rational> pUpper, int pHandle, Rational pEpsilon) {
    return cache.storeFormulaUpper(pFormula, pUpper, pHandle, pEpsilon);
  }

  @Override
  public Optional<Rational> getFormulaUpper(Formula pFormula, int pHandle, Rational pEpsilon) {
    return cache.getFormulaUpper(pFormula, pHandle, pEpsilon);
  }

  @Override
  public Optional<Rational> storeFormulaLower(
      Formula pFormula, Optional<Rational> pLower, int pHandle, Rational pEpsilon) {
    return cache.storeFormulaLower(pFormula, pLower, pHandle, pEpsilon);
  }

  @Override
  public Optional<Rational> getFormulaLower(Formula pFormula, int pHandle, Rational pEpsilon) {
    return cache.getFormulaLower(pFormula, pHandle, pEpsilon);
  }

  @Override
  public void close() {
    if (cache != null) {
      writeCacheFile(cache);
      cache = null;
    }
  }

  @Override
  public List<List<Formula>> storeAllSat(
      Formula pFormula, List<Formula> pImportant, List<List<Formula>> pCached) {
    return cache.storeAllSat(pFormula, pImportant, pCached);
  }

  @Override
  public List<List<Formula>> getAllSat(Formula pFormula, List<Formula> pImportant) {
    return cache.getAllSat(pFormula, pImportant);
  }

  private void writeCacheFile(InMemorySMTCache pCache) {
    if (fileName != null && Files.exists(fileName) && Files.isWritable(fileName)) {
      writeToFile(pCache, tempFileLocation);
      try {
        Files.move(tempFileLocation, fileName, StandardCopyOption.REPLACE_EXISTING);
      } catch (IOException e) {
        throw new RuntimeException("Could not overwrite SMT-cachefile on disc.", e);
      }
    } else {
      writeToFile(pCache, fileName);
    }
  }

  private void writeToFile(InMemorySMTCache pCache, Path check) {
    createParentDirectoryIfNecessary(check);

    try (ObjectOutputStream os = new ObjectOutputStream(Files.newOutputStream(check))) {
      os.writeObject(pCache);
    } catch (Exception e) {
      throw new RuntimeException("Could not write SMT-cachefile to disc.", e);
    }
  }

  private void createParentDirectoryIfNecessary(Path check) {
    if (!Files.exists(check.getParent())) {
      try {
        MoreFiles.createParentDirectories(check);
      } catch (IOException e) {
        throw new RuntimeException(
            "Could not create directory "
                + check.getParent().getFileName()
                + " for write into "
                + check.toAbsolutePath(),
            e);
      }
    }
  }
}
