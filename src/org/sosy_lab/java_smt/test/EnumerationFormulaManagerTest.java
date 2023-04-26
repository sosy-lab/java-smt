// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import com.google.common.collect.Sets;
import java.util.Set;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;
import org.sosy_lab.java_smt.api.SolverException;

@RunWith(Parameterized.class)
public class EnumerationFormulaManagerTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Before
  public void init() {
    requireEnumeration();
  }

  @Test
  public void testEnumerationDeclaration() {
    Set<String> colors = Sets.newHashSet("Blue", "White");
    EnumerationFormulaType colorType = emgr.declareEnumeration("Color", "Blue", "White");
    assertThat(colorType.getName()).isEqualTo("Color");
    assertThat(colorType.getElements()).isEqualTo(colors);

    Set<String> shapes = Sets.newHashSet("Circle", "Square", "Triangle");
    EnumerationFormulaType shapeType = emgr.declareEnumeration("Shape", shapes);
    assertThat(shapeType.getName()).isEqualTo("Shape");
    assertThat(shapeType.getElements()).isEqualTo(shapes);

    assertThat(colors).isNotEqualTo(shapes);
  }

  @Test
  public void testTooManyDistinctValues() throws SolverException, InterruptedException {
    EnumerationFormulaType colorType = emgr.declareEnumeration("ColorA", "Blue", "White");
    EnumerationFormula color1 = emgr.makeVariable("first", colorType);
    EnumerationFormula color2 = emgr.makeVariable("second", colorType);
    EnumerationFormula color3 = emgr.makeVariable("third", colorType);

    // there are two colors, so there can be two distinct assignments.
    assertThatFormula(bmgr.not(emgr.equivalence(color1, color2))).isSatisfiable();
    assertThatFormula(bmgr.not(emgr.equivalence(color2, color3))).isSatisfiable();
    assertThatFormula(bmgr.not(emgr.equivalence(color3, color1))).isSatisfiable();

    // there are only two colors, so there can not be three distinct assignments.
    assertThatFormula(
            bmgr.and(
                bmgr.not(emgr.equivalence(color1, color2)),
                bmgr.not(emgr.equivalence(color2, color3)),
                bmgr.not(emgr.equivalence(color3, color1))))
        .isUnsatisfiable();
  }

  @Test
  public void testConstants() throws SolverException, InterruptedException {
    EnumerationFormulaType colorType = emgr.declareEnumeration("ColorB", "Blue", "White");
    EnumerationFormula blue = emgr.makeConstant("Blue", colorType);
    EnumerationFormula white = emgr.makeConstant("White", colorType);
    EnumerationFormula var = emgr.makeVariable("var", colorType);

    assertThatFormula(emgr.equivalence(blue, var)).isSatisfiable();
    assertThatFormula(emgr.equivalence(white, var)).isSatisfiable();
    assertThatFormula(bmgr.not(emgr.equivalence(blue, var))).isSatisfiable();
    assertThatFormula(bmgr.not(emgr.equivalence(white, var))).isSatisfiable();
    assertThatFormula(bmgr.not(emgr.equivalence(blue, white))).isSatisfiable();

    // there are only two colors, so is no third option.
    assertThatFormula(
            bmgr.or(bmgr.not(emgr.equivalence(blue, var)), bmgr.not(emgr.equivalence(white, var))))
        .isUnsatisfiable();
    assertThatFormula(bmgr.or(emgr.equivalence(blue, var), emgr.equivalence(white, var)))
        .isUnsatisfiable();
    assertThatFormula(
            bmgr.and(bmgr.not(emgr.equivalence(blue, var)), bmgr.not(emgr.equivalence(white, var))))
        .isUnsatisfiable();
    assertThatFormula(bmgr.and(emgr.equivalence(blue, var), emgr.equivalence(white, var)))
        .isUnsatisfiable();
  }

  @Test
  public void testIncompatibleEnumeration() {
    EnumerationFormulaType colorType = emgr.declareEnumeration("ColorC", "Blue", "White");
    EnumerationFormulaType shapeType =
        emgr.declareEnumeration("ShapeC", "Circle", "Rectangle", "Triangle");

    EnumerationFormula blue = emgr.makeConstant("Blue", colorType);
    EnumerationFormula varColor = emgr.makeVariable("varColor", colorType);

    EnumerationFormula circle = emgr.makeConstant("Circle", shapeType);
    EnumerationFormula varShape = emgr.makeVariable("varShape", shapeType);

    Assert.assertThrows(IllegalArgumentException.class, () -> emgr.equivalence(blue, varShape));
    Assert.assertThrows(IllegalArgumentException.class, () -> emgr.equivalence(circle, varColor));
    Assert.assertThrows(IllegalArgumentException.class, () -> emgr.equivalence(varColor, varShape));
    Assert.assertThrows(IllegalArgumentException.class, () -> emgr.equivalence(blue, circle));
  }

  @Test
  public void testInvalidName() {
    Assert.assertThrows(
        IllegalArgumentException.class, () -> emgr.declareEnumeration("true", "X", "Y"));
    EnumerationFormulaType colorType = emgr.declareEnumeration("ColorE", "Blue", "White");
    Assert.assertThrows(IllegalArgumentException.class, () -> emgr.makeVariable("true", colorType));
  }
}
