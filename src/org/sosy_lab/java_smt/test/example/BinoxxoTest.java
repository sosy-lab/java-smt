// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test.example;

import static com.google.common.truth.Truth.assertThat;

import java.util.Arrays;
import org.junit.Test;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.example.Binoxxo.BinoxxoSolver;
import org.sosy_lab.java_smt.example.Binoxxo.BooleanBasedBinoxxoSolver;

public class BinoxxoTest {

  @Test
  public void testBinoxxo10()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    String[] input = {
      "..X.X...X.",
      ".....XX...",
      "..........",
      ".O.O..X..X",
      ".....X..XX",
      "......O...",
      "......O.XO",
      "..........",
      ".......O.O",
      "....X....O",
    };
    String[] expected = {
      "OOXOXOXOXX",
      "OOXOOXXOXX",
      "XXOXOXOXOO",
      "OOXOXOXXOX",
      "OOXOOXXOXX",
      "XXOXXOOXOO",
      "XXOXOXOOXO",
      "OOXOXOXXOX",
      "XXOXOXOOXO",
      "XXOXXOOXOO",
    };
    checkBinoxxo(input, expected);
  }

  @Test
  public void testBinoxxo12()
      throws InvalidConfigurationException, SolverException, InterruptedException {
    String[] input = {
      "O..OO..X......",
      "O..O..O.X.....",
      "........X.....",
      "O...XX.....O..",
      "........X.X..X",
      "..XX.O.O...O..",
      "....X.X.....X.",
      "..X....X...O..",
      "..X......O..OO",
      ".X..O.........",
      "..O.O...O.X...",
      ".X...OO......X",
      "..........OO..",
      ".X......X.....",
    };
    String[] expected = {
      "OOXOOXOXOXXOXX",
      "OXOOXOOXXOXXOX",
      "XOOXOOXOXXOXXO",
      "OOXOXXOXOXOOXX",
      "OXOOXXOOXOXXOX",
      "XOXXOOXOXXOOXO",
      "OXOOXOXXOXOXXO",
      "XOXXOXOXOOXOOX",
      "OXXOXOXOXOXXOO",
      "XXOXOXXOOXOOXO",
      "XOOXOXOXOOXXOX",
      "OXXOXOOXXOXOOX",
      "XOXXOXXOOXOOXO",
      "XXOXXOXOXOOXOO",
    };
    checkBinoxxo(input, expected);
  }

  private void checkBinoxxo(String[] input, String[] expected)
      throws InvalidConfigurationException, InterruptedException, SolverException {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();
    try (SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, notifier, Solvers.Z3)) {
      BinoxxoSolver<?> binoxxo = new BooleanBasedBinoxxoSolver(context);
      assertThat(binoxxo.solve(fromString(input))).isEqualTo(fromString(expected));
    }
  }

  private char[][] fromString(String[] grid) {
    return Arrays.stream(grid).map(String::toCharArray).toArray(char[][]::new);
  }
}
