// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.api.FormulaType.getArrayType;

import com.google.common.base.Strings;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;
import com.google.common.truth.Truth;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;
import java.util.stream.Stream;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.DefaultBooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

public class SolverVisitorTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  /** visit a formula and fail on OTHER, i.e., unexpected function declaration type. */
  private final class FunctionDeclarationVisitorNoOther
      extends DefaultFormulaVisitor<List<FunctionDeclarationKind>> {

    private final List<FunctionDeclarationKind> found = new ArrayList<>();

    @Override
    public List<FunctionDeclarationKind> visitFunction(
        Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
      found.add(functionDeclaration.getKind());
      Truth.assert_()
          .withMessage(
              "unexpected declaration kind '%s' in function '%s' with args '%s'.",
              functionDeclaration, f, args)
          .that(functionDeclaration.getKind())
          .isNotEqualTo(FunctionDeclarationKind.OTHER);
      for (Formula arg : args) {
        mgr.visit(arg, this);
      }
      return visitDefault(f);
    }

    @Override
    protected List<FunctionDeclarationKind> visitDefault(Formula pF) {
      return found;
    }
  }

  /** visit a formula and fail on UF, i.e., uninterpreted function declaration type. */
  private final class FunctionDeclarationVisitorNoUF
      extends DefaultFormulaVisitor<List<FunctionDeclarationKind>> {

    private final List<FunctionDeclarationKind> found = new ArrayList<>();

    @Override
    public List<FunctionDeclarationKind> visitFunction(
        Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
      found.add(functionDeclaration.getKind());
      Truth.assert_()
          .withMessage(
              "uninterpreted function declaration '%s' in function '%s' with args '%s'.",
              functionDeclaration, f, args)
          .that(functionDeclaration.getKind())
          .isNotEqualTo(FunctionDeclarationKind.UF);
      for (Formula arg : args) {
        mgr.visit(arg, this);
      }
      return visitDefault(f);
    }

    @Override
    protected List<FunctionDeclarationKind> visitDefault(Formula pF) {
      return found;
    }
  }

  /** visit only constants and ignore other operations. */
  private final class ConstantsVisitor extends DefaultFormulaVisitor<List<Object>> {

    private final boolean recursive;
    private final List<Object> found = new ArrayList<>();

    ConstantsVisitor(boolean recursive) {
      this.recursive = recursive;
    }

    ConstantsVisitor() {
      this.recursive = false;
    }

    @Override
    public List<Object> visitConstant(Formula f, Object value) {
      found.add(value);
      return visitDefault(f);
    }

    @Override
    public List<Object> visitFunction(
        Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
      if (recursive) {
        for (Formula arg : args) {
          mgr.visit(arg, this);
        }
      }
      return visitDefault(f);
    }

    @Override
    protected List<Object> visitDefault(Formula pF) {
      return found;
    }
  }

  @Before
  public void setup() {
    requireVisitor();
  }

  @Test
  public void booleanIdVisit() {
    BooleanFormula t = bmgr.makeBoolean(true);
    BooleanFormula f = bmgr.makeBoolean(false);
    BooleanFormula x = bmgr.makeVariable("x");
    BooleanFormula y = bmgr.makeVariable("y");
    BooleanFormula z = bmgr.makeVariable("z");
    BooleanFormula and = bmgr.and(x, y);
    BooleanFormula or = bmgr.or(x, y);
    BooleanFormula ite = bmgr.ifThenElse(x, and, or);
    BooleanFormula impl = bmgr.implication(z, y);
    BooleanFormula eq = bmgr.equivalence(t, y);
    BooleanFormula not = bmgr.not(eq);

    for (BooleanFormula bf : ImmutableList.of(t, f, x, y, z, and, or, ite, impl, eq, not)) {
      BooleanFormulaVisitor<BooleanFormula> identityVisitor =
          new BooleanFormulaTransformationVisitor(mgr) {
            // we need a subclass, because the original class is 'abstract'
          };
      assertThatFormula(bmgr.visit(bf, identityVisitor)).isEqualTo(bf);
    }
  }

  @Test
  public void bitvectorIdVisit() throws SolverException, InterruptedException {
    requireBitvectors();
    BitvectorType bv8 = FormulaType.getBitvectorTypeWithSize(8);
    BitvectorFormula x = bvmgr.makeVariable(bv8, "x");
    BitvectorFormula y1 = bvmgr.makeVariable(bv8, "y");
    BitvectorFormula y2 = bvmgr.add(y1, bvmgr.makeBitvector(8, 13));
    BitvectorFormula y3 = bvmgr.makeBitvector(8, 13);

    for (BitvectorFormula y : new BitvectorFormula[] {y1, y2, y3}) {
      for (BooleanFormula f :
          ImmutableList.of(
              bvmgr.equal(x, y),
              bmgr.not(bvmgr.equal(x, y)),
              bvmgr.lessThan(x, y, true),
              bvmgr.lessThan(x, y, false),
              bvmgr.lessOrEquals(x, y, true),
              bvmgr.lessOrEquals(x, y, false),
              bvmgr.greaterThan(x, y, true),
              bvmgr.greaterThan(x, y, false),
              bvmgr.greaterOrEquals(x, y, true),
              bvmgr.greaterOrEquals(x, y, false))) {
        mgr.visit(f, new FunctionDeclarationVisitorNoUF());
        if (Solvers.PRINCESS != solver) {
          // Princess models BV theory with intervals, such as "mod_cast(lower, upper , value)".
          // The interval function is of FunctionDeclarationKind.OTHER and thus we cannot check it.
          mgr.visit(f, new FunctionDeclarationVisitorNoOther());
        }
        BooleanFormula f2 = mgr.transformRecursively(f, new FormulaTransformationVisitor(mgr) {});
        assertThat(f2).isEqualTo(f);
        assertThatFormula(f).isEquivalentTo(f2);
      }
      for (BitvectorFormula f :
          ImmutableList.of(
              bvmgr.add(x, y),
              bvmgr.subtract(x, y),
              bvmgr.multiply(x, y),
              bvmgr.and(x, y),
              bvmgr.or(x, y),
              bvmgr.xor(x, y),
              bvmgr.divide(x, y, true),
              bvmgr.divide(x, y, false),
              bvmgr.remainder(x, y, true),
              bvmgr.remainder(x, y, false),
              bvmgr.smodulo(x, y),
              bvmgr.not(x),
              bvmgr.negate(x),
              bvmgr.extract(x, 7, 5),
              bvmgr.extract(x, 7, 5),
              bvmgr.concat(x, y))) {
        mgr.visit(f, new FunctionDeclarationVisitorNoUF());
        if (Solvers.PRINCESS != solver) {
          // Princess models BV theory with intervals, such as "mod_cast(lower, upper , value)".
          // The interval function is of FunctionDeclarationKind.OTHER and thus we cannot check it.
          mgr.visit(f, new FunctionDeclarationVisitorNoOther());
        }
        BitvectorFormula f2 = mgr.transformRecursively(f, new FormulaTransformationVisitor(mgr) {});
        assertThat(f2).isEqualTo(f);
        assertThatFormula(bmgr.not(bvmgr.equal(f, f2))).isUnsatisfiable();
      }
    }
  }

  @Test
  public void bitvectorIdVisit2() throws SolverException, InterruptedException {
    requireBitvectors();
    BitvectorFormula n = bvmgr.makeBitvector(8, 13);

    for (BitvectorFormula f : new BitvectorFormula[] {n}) {
      mgr.visit(f, new FunctionDeclarationVisitorNoUF());
      if (Solvers.PRINCESS != solver) {
        // Princess models BV theory with intervals, such as "mod_cast(lower, upper , value)".
        // The interval function is of FunctionDeclarationKind.OTHER and thus we cannot check it.
        mgr.visit(f, new FunctionDeclarationVisitorNoOther());
      }
      BitvectorFormula f2 = mgr.transformRecursively(f, new FormulaTransformationVisitor(mgr) {});
      assertThat(f2).isEqualTo(f);
      assertThatFormula(bmgr.not(bvmgr.equal(f, f2))).isUnsatisfiable();
    }
  }

  @Test
  public void integerConstantVisit() {
    requireIntegers();
    for (long n :
        new long[] {
          0, 1, 2, 17, 127, 255, -1, -2, -17, -127, 127000, 255000, -100, -200, -1700, -127000,
          -255000,
        }) {
      ConstantsVisitor visitor = new ConstantsVisitor();
      mgr.visit(imgr.makeNumber(n), visitor);
      assertThat(visitor.found).containsExactly(BigInteger.valueOf(n));
    }
  }

  @Test
  public void rationalConstantVisit() {
    requireRationals();
    for (long n :
        new long[] {
          0, 1, 2, 17, 127, 255, -1, -2, -17, -127, 127000, 255000, -100, -200, -1700, -127000,
          -255000,
        }) {
      ConstantsVisitor visitor = new ConstantsVisitor();
      mgr.visit(rmgr.makeNumber(n), visitor); // normal integers as rationals
      assertThat(visitor.found).containsExactly(BigInteger.valueOf(n));
    }
    for (long n :
        new long[] {
          1, 2, 17, 127, 255, -1, -2, -17, -127, 127000, 255000, -100, -200, -1700, -127000,
          -255000,
        }) {
      ConstantsVisitor visitor = new ConstantsVisitor();
      mgr.visit(rmgr.makeNumber(Rational.ofLongs(n, 321)), visitor);
      assertThat(visitor.found).containsExactly(Rational.ofLongs(n, 321));
    }
  }

  @Test
  public void arrayVisit() {
    requireArrays();
    requireIntegers();

    ArrayFormulaType<IntegerFormula, IntegerFormula> arrayType =
        getArrayType(FormulaType.IntegerType, FormulaType.IntegerType);
    IntegerFormula index = imgr.makeNumber(1);
    IntegerFormula elem = imgr.makeNumber(123);

    ArrayFormula<IntegerFormula, IntegerFormula> arr = amgr.makeArray("some_array", arrayType);
    IntegerFormula selectedElem = amgr.select(arr, index);
    assertThat(mgr.visit(selectedElem, new FunctionDeclarationVisitorNoOther()))
        .containsExactly(FunctionDeclarationKind.SELECT);
    assertThat(mgr.visit(selectedElem, new ConstantsVisitor(true)))
        .containsExactly(BigInteger.valueOf(1));

    ArrayFormula<IntegerFormula, IntegerFormula> store = amgr.store(arr, index, elem);
    assertThat(mgr.visit(store, new FunctionDeclarationVisitorNoOther()))
        .containsExactly(FunctionDeclarationKind.STORE);
    assertThat(mgr.visit(store, new ConstantsVisitor(true)))
        .containsExactly(BigInteger.valueOf(1), BigInteger.valueOf(123));

    assume()
        .withMessage("Solver %s does not support initialization of arrays", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.OPENSMT);

    ArrayFormula<IntegerFormula, IntegerFormula> initializedArr = amgr.makeArray(arrayType, elem);
    assertThat(mgr.visit(initializedArr, new FunctionDeclarationVisitorNoOther()))
        .containsExactly(FunctionDeclarationKind.CONST);
    assertThat(mgr.visit(initializedArr, new ConstantsVisitor(true)))
        .containsExactly(BigInteger.valueOf(123));
  }

  @Test
  public void arrayTransform() throws SolverException, InterruptedException {
    requireArrays();
    requireArrays();

    ArrayFormulaType<IntegerFormula, IntegerFormula> arrayType =
        getArrayType(FormulaType.IntegerType, FormulaType.IntegerType);
    IntegerFormula index = imgr.makeNumber(1);
    IntegerFormula elem = imgr.makeNumber(123);
    IntegerFormula x = imgr.makeVariable("some_var");

    ArrayFormula<IntegerFormula, IntegerFormula> arr = amgr.makeArray("some_array", arrayType);
    BooleanFormula f = imgr.equal(amgr.select(arr, index), x);
    BooleanFormula f2 = mgr.transformRecursively(f, new FormulaTransformationVisitor(mgr) {});
    assertThat(f2).isEqualTo(f);
    assertThatFormula(f).isEquivalentTo(f2);

    BooleanFormula f3 = amgr.equivalence(amgr.store(arr, index, elem), arr);
    BooleanFormula f4 = mgr.transformRecursively(f3, new FormulaTransformationVisitor(mgr) {});
    assertThat(f4).isEqualTo(f3);
    assertThatFormula(f3).isEquivalentTo(f4);

    assume()
        .withMessage("Solver %s does not support initialization of arrays", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.OPENSMT);

    BooleanFormula f5 = amgr.equivalence(amgr.makeArray(arrayType, elem), arr);
    BooleanFormula f6 = mgr.transformRecursively(f5, new FormulaTransformationVisitor(mgr) {});
    assertThat(f6).isEqualTo(f5);
    assertThatFormula(f5).isEquivalentTo(f6);
  }

  @Test
  public void bitvectorConstantVisit() {
    requireBitvectors();

    // check small bitsize
    for (long n : new long[] {0, 1, 2, 17, 99, 127, 255}) {
      ConstantsVisitor visitor = new ConstantsVisitor();
      mgr.visit(bvmgr.makeBitvector(8, n), visitor);
      assertThat(visitor.found).containsExactly(BigInteger.valueOf(n));
    }
    for (long n : new long[] {-1, -2, -17, -99, -127}) {
      ConstantsVisitor visitor = new ConstantsVisitor();
      mgr.visit(bvmgr.makeBitvector(8, n), visitor);
      assertThat(visitor.found)
          .containsExactly(BigInteger.ONE.shiftLeft(8).add(BigInteger.valueOf(n)));
    }

    // check normal bitsize
    for (long n : new long[] {0, 100, 200, 1700, 99000, 127000, 255000}) {
      ConstantsVisitor visitor = new ConstantsVisitor();
      mgr.visit(bvmgr.makeBitvector(32, n), visitor);
      assertThat(visitor.found).containsExactly(BigInteger.valueOf(n));
    }
    for (long n : new long[] {-100, -200, -1700, -99000, -127000, -255000}) {
      ConstantsVisitor visitor = new ConstantsVisitor();
      mgr.visit(bvmgr.makeBitvector(32, n), visitor);
      assertThat(visitor.found)
          .containsExactly(BigInteger.ONE.shiftLeft(32).add(BigInteger.valueOf(n)));
    }
  }

  @Test
  public void floatConstantVisit() {
    requireFloats();

    var testValues =
        ImmutableMap.<Double, String>builder()
            .put(Double.NEGATIVE_INFINITY, "1111110000000000")
            .put(-1d, "1011110000000000")
            .put(-2d, "1100000000000000")
            .put(0.0, "0000000000000000")
            .put(-0.0, "1000000000000000")
            .put(0.00001, "0000000010101000")
            .put(1d, "0011110000000000")
            .put(2d, "0100000000000000")
            .put(5.32, "0100010101010010")
            .put(10d, "0100100100000000")
            .put(Double.POSITIVE_INFINITY, "0111110000000000")
            .buildOrThrow();

    for (Entry<Double, String> entry : testValues.entrySet()) {
      checkFloatConstant(
          FormulaType.getDoublePrecisionFloatingPointType(),
          entry.getKey(),
          Strings.padStart(
              Long.toBinaryString(Double.doubleToRawLongBits(entry.getKey())), 64, '0'));
      checkFloatConstant(
          FormulaType.getSinglePrecisionFloatingPointType(),
          entry.getKey().floatValue(),
          Strings.padStart(
              Integer.toBinaryString(Float.floatToRawIntBits(entry.getKey().floatValue())),
              32,
              '0'));
      checkFloatConstant(FormulaType.getFloatingPointType(5, 10), entry.getKey(), entry.getValue());
    }
  }

  private void checkFloatConstant(FloatingPointType prec, double value, String bits) {
    FloatingPointNumber fp =
        FloatingPointNumber.of(bits, prec.getExponentSize(), prec.getMantissaSize());

    ConstantsVisitor visitor = new ConstantsVisitor();
    mgr.visit(fpmgr.makeNumber(value, prec), visitor);
    assertThat(visitor.found).containsExactly(fp);

    ConstantsVisitor visitor2 = new ConstantsVisitor();
    mgr.visit(fpmgr.makeNumber(fp.getExponent(), fp.getMantissa(), fp.getSign(), prec), visitor2);
    assertThat(visitor2.found).containsExactly(fp);
  }

  @Test
  public void floatIdVisit() {
    requireFloats();
    FloatingPointType fp = FormulaType.getSinglePrecisionFloatingPointType();
    FloatingPointFormula x = fpmgr.makeVariable("x", fp);
    FloatingPointFormula y = fpmgr.makeVariable("y", fp);

    for (Formula f :
        ImmutableList.of(
            fpmgr.equalWithFPSemantics(x, y),
            fpmgr.add(x, y),
            fpmgr.subtract(x, y),
            fpmgr.multiply(x, y),
            fpmgr.lessThan(x, y),
            fpmgr.lessOrEquals(x, y),
            fpmgr.greaterThan(x, y),
            fpmgr.greaterOrEquals(x, y),
            fpmgr.divide(x, y),
            fpmgr.round(x, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN),
            // fpmgr.round(x, FloatingPointRoundingMode.NEAREST_TIES_AWAY),
            fpmgr.round(x, FloatingPointRoundingMode.TOWARD_POSITIVE),
            fpmgr.round(x, FloatingPointRoundingMode.TOWARD_NEGATIVE),
            fpmgr.round(x, FloatingPointRoundingMode.TOWARD_ZERO))) {
      mgr.visit(f, new FunctionDeclarationVisitorNoOther());
      mgr.visit(f, new FunctionDeclarationVisitorNoUF());
      Formula f2 = mgr.transformRecursively(f, new FormulaTransformationVisitor(mgr) {});
      assertThat(f2).isEqualTo(f);
    }
  }

  @Test
  public void floatMoreVisit() {
    requireFloats();
    requireBitvectors();
    FloatingPointType fp = FormulaType.getSinglePrecisionFloatingPointType();
    FloatingPointFormula x = fpmgr.makeVariable("x", fp);
    FloatingPointFormula y = fpmgr.makeVariable("x", fp);
    BitvectorFormula z = bvmgr.makeVariable(32, "z");

    checkKind(
        fpmgr.castTo(x, true, FormulaType.getBitvectorTypeWithSize(32)),
        FunctionDeclarationKind.FP_CASTTO_SBV);
    checkKind(
        fpmgr.castTo(x, true, FormulaType.getDoublePrecisionFloatingPointType()),
        FunctionDeclarationKind.FP_CASTTO_FP);
    checkKind(
        fpmgr.castTo(x, false, FormulaType.getBitvectorTypeWithSize(32)),
        FunctionDeclarationKind.FP_CASTTO_UBV);
    checkKind(
        fpmgr.castTo(x, false, FormulaType.getDoublePrecisionFloatingPointType()),
        FunctionDeclarationKind.FP_CASTTO_FP);
    checkKind(fpmgr.isNaN(x), FunctionDeclarationKind.FP_IS_NAN);
    checkKind(fpmgr.isNegative(x), FunctionDeclarationKind.FP_IS_NEGATIVE);
    checkKind(fpmgr.isInfinity(x), FunctionDeclarationKind.FP_IS_INF);
    checkKind(fpmgr.isNormal(x), FunctionDeclarationKind.FP_IS_NORMAL);
    checkKind(fpmgr.isSubnormal(x), FunctionDeclarationKind.FP_IS_SUBNORMAL);
    checkKind(fpmgr.isZero(x), FunctionDeclarationKind.FP_IS_ZERO);
    checkKind(fpmgr.abs(x), FunctionDeclarationKind.FP_ABS);
    checkKind(fpmgr.max(x, y), FunctionDeclarationKind.FP_MAX);
    checkKind(fpmgr.min(x, y), FunctionDeclarationKind.FP_MIN);
    checkKind(fpmgr.sqrt(x), FunctionDeclarationKind.FP_SQRT);
    if (!List.of(Solvers.CVC4, Solvers.CVC5, Solvers.BITWUZLA)
        .contains(solverToUse())) { // CVC4/CVC5 and bitwuzla do not support this operation
      // On Bitwuzla we replaces "fp_to_bv(fpTerm)" with "newVar" and the adds the assertion
      // "fpTerm = bv_to_fp(newVar)" as a side condition. Unfortunately this workaround will not
      // work for this test.
      checkKind(fpmgr.toIeeeBitvector(x), FunctionDeclarationKind.FP_AS_IEEEBV);
    }
    checkKind(
        fpmgr.castFrom(z, true, FormulaType.getSinglePrecisionFloatingPointType()),
        FunctionDeclarationKind.BV_SCASTTO_FP);
    checkKind(
        fpmgr.castFrom(z, false, FormulaType.getSinglePrecisionFloatingPointType()),
        FunctionDeclarationKind.BV_UCASTTO_FP);
  }

  @Test
  public void fpToBvTest() {
    requireFloats();
    requireBitvectors();
    assume()
        .withMessage("FP-to-BV conversion not available for CVC4 and CVC5")
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5);

    var fpType = FormulaType.getFloatingPointType(5, 10);
    var visitor =
        new DefaultFormulaVisitor<Void>() {
          @Override
          protected Void visitDefault(Formula f) {
            return null;
          }
        };

    for (int num : List.of(0, 1, 4, 16, 256, 1024)) {
      Formula bv2fp = fpmgr.fromIeeeBitvector(bvmgr.makeBitvector(16, num), fpType);
      mgr.visit(bv2fp, visitor);
      Formula fp2bv = fpmgr.toIeeeBitvector(fpmgr.makeNumber(num, fpType));
      mgr.visit(fp2bv, visitor);
    }
  }

  @Test
  public void bvVisit() throws SolverException, InterruptedException {
    requireBitvectors();
    BitvectorFormula x = bvmgr.makeVariable(5, "x");

    for (BitvectorFormula f :
        ImmutableList.of(bvmgr.extend(x, 10, true), bvmgr.extend(x, 10, false))) {
      BitvectorFormula f2 = mgr.transformRecursively(f, new FormulaTransformationVisitor(mgr) {});
      assertThat(f2).isEqualTo(f);
      assertThatFormula(bmgr.not(bvmgr.equal(f, f2))).isUnsatisfiable();
    }
  }

  @Test
  public void bvVisitFunctionArgs() {
    requireBitvectors();
    BitvectorFormula x = bvmgr.makeVariable(5, "x");
    BitvectorFormula y = bvmgr.makeVariable(5, "y");

    final List<Formula> formulas =
        Lists.newArrayList(
            bvmgr.lessOrEquals(x, y, true),
            bvmgr.lessOrEquals(x, y, false),
            bvmgr.lessThan(x, y, true),
            bvmgr.lessThan(x, y, false),
            bvmgr.greaterOrEquals(x, y, true),
            bvmgr.greaterOrEquals(x, y, false),
            bvmgr.greaterThan(x, y, true),
            bvmgr.greaterThan(x, y, false),
            bvmgr.add(x, y),
            bvmgr.subtract(x, y),
            bvmgr.multiply(x, y),
            bvmgr.divide(x, y, true),
            bvmgr.divide(x, y, false),
            bvmgr.remainder(x, y, true),
            bvmgr.remainder(x, y, false),
            bvmgr.and(x, y),
            bvmgr.or(x, y),
            bvmgr.xor(x, y),
            bvmgr.equal(x, y),
            bvmgr.not(x),
            bvmgr.negate(y));
    if (Solvers.MATHSAT5 != solver) {
      formulas.add(bvmgr.smodulo(x, y));
    }

    for (Formula f : formulas) {
      mgr.visitRecursively(
          f,
          new DefaultFormulaVisitor<>() {

            @Override
            protected TraversalProcess visitDefault(Formula pF) {
              return TraversalProcess.CONTINUE;
            }

            @Override
            public TraversalProcess visitFunction(
                Formula pF, List<Formula> pArgs, FunctionDeclaration<?> pDeclaration) {
              switch (pDeclaration.getKind()) {
                case NOT:
                  assertThat(pArgs).hasSize(1);
                  break;
                case ITE:
                  assertThat(pArgs).hasSize(3);
                  break;
                case EQ:
                case BV_SLT:
                case BV_SLE:
                case BV_SGT:
                case BV_SGE:
                case BV_ULT:
                case BV_ULE:
                case BV_UGT:
                case BV_UGE:
                  assertThat(pArgs).hasSize(2);
                  break;
                case BV_NOT:
                case BV_NEG:
                  // Yices is special in some cases
                  if (Solvers.YICES2 != solverToUse()) {
                    assertThat(pArgs).hasSize(1);
                  }
                  break;
                case BV_ADD:
                  assertThat(pArgs).contains(x);
                  assertThat(pArgs).hasSize(2);
                  break;
                case BV_MUL:
                  assertThat(pArgs).contains(y);
                  assertThat(pArgs).hasSize(2);
                  if (Solvers.YICES2 != solverToUse()) {
                    assertThat(pArgs).contains(x);
                  }
                  break;
                default:
                  if (Solvers.YICES2 != solverToUse()) {
                    assertThat(pArgs).hasSize(2);
                    assertThat(pArgs).containsExactly(x, y);
                  }
              }
              return visitDefault(pF);
            }
          });
    }
  }

  @Test
  public void stringInBooleanFormulaIdVisit() throws SolverException, InterruptedException {
    requireStrings();
    StringFormula x = smgr.makeVariable("xVariable");
    StringFormula y = smgr.makeVariable("yVariable");
    RegexFormula r = smgr.makeRegex("regex1");

    for (BooleanFormula f :
        ImmutableList.of(
            smgr.equal(x, y),
            smgr.contains(x, y),
            smgr.lessThan(x, y),
            smgr.lessOrEquals(x, y),
            smgr.greaterOrEquals(x, y),
            smgr.greaterThan(x, y),
            smgr.prefix(x, y),
            smgr.suffix(x, y),
            smgr.in(x, r))) {
      mgr.visit(f, new FunctionDeclarationVisitorNoUF());
      mgr.visit(f, new FunctionDeclarationVisitorNoOther());
      BooleanFormula f2 = mgr.transformRecursively(f, new FormulaTransformationVisitor(mgr) {});
      assertThat(f2).isEqualTo(f);
      assertThatFormula(f).isEquivalentTo(f2);
    }
  }

  @Test
  public void stringInStringFormulaVisit() throws SolverException, InterruptedException {
    requireStrings();
    StringFormula x = smgr.makeVariable("xVariable");
    StringFormula y = smgr.makeVariable("yVariable");
    StringFormula z = smgr.makeString("zAsString");
    IntegerFormula offset = imgr.makeVariable("offset");
    IntegerFormula len = imgr.makeVariable("len");

    ImmutableList.Builder<StringFormula> formulas =
        ImmutableList.<StringFormula>builder()
            .add(smgr.substring(x, offset, len))
            .add(smgr.replace(x, y, z))
            .add(smgr.charAt(x, offset))
            .add(smgr.toStringFormula(offset))
            .add(smgr.concat(x, y, z));
    if (solverToUse() != Solvers.Z3) {
      formulas.add(smgr.replaceAll(x, y, z)); // unsupported in Z3
    }
    for (StringFormula f : formulas.build()) {
      mgr.visit(f, new FunctionDeclarationVisitorNoUF());
      mgr.visit(f, new FunctionDeclarationVisitorNoOther());
      StringFormula f2 = mgr.transformRecursively(f, new FormulaTransformationVisitor(mgr) {});
      assertThat(f2).isEqualTo(f);
      assertThatFormula(bmgr.not(smgr.equal(f, f2))).isUnsatisfiable();
    }
  }

  @Test
  public void stringInRegexFormulaVisit() {
    requireStrings();
    RegexFormula r = smgr.makeRegex("regex1");
    RegexFormula s = smgr.makeRegex("regex2");

    ImmutableList.Builder<RegexFormula> formulas =
        ImmutableList.<RegexFormula>builder()
            .add(smgr.union(r, s))
            .add(smgr.closure(r))
            .add(smgr.concat(r, r, r, s, s, s))
            .add(smgr.cross(r));
    if (solverToUse() != Solvers.Z3) {
      formulas.add(smgr.difference(r, s)).add(smgr.complement(r));
      // invalid function OTHER/INTERNAL in visitor, bug in Z3?
    }
    for (RegexFormula f : formulas.build()) {
      mgr.visit(f, new FunctionDeclarationVisitorNoUF());
      mgr.visit(f, new FunctionDeclarationVisitorNoOther());
      RegexFormula f2 = mgr.transformRecursively(f, new FormulaTransformationVisitor(mgr) {});
      assertThat(f2).isEqualTo(f);
    }
  }

  @Test
  public void stringInIntegerFormulaVisit() throws SolverException, InterruptedException {
    requireStrings();
    StringFormula x = smgr.makeVariable("xVariable");
    StringFormula y = smgr.makeVariable("yVariable");
    IntegerFormula offset = imgr.makeVariable("offset");

    for (IntegerFormula f :
        ImmutableList.of(smgr.indexOf(x, y, offset), smgr.length(x), smgr.toIntegerFormula(x))) {
      mgr.visit(f, new FunctionDeclarationVisitorNoUF());
      mgr.visit(f, new FunctionDeclarationVisitorNoOther());
      IntegerFormula f2 = mgr.transformRecursively(f, new FormulaTransformationVisitor(mgr) {});
      assertThat(f2).isEqualTo(f);
      assertThatFormula(bmgr.not(imgr.equal(f, f2))).isUnsatisfiable();
    }
  }

  private void checkKind(Formula f, FunctionDeclarationKind expected) {
    FunctionDeclarationVisitorNoOther visitor = new FunctionDeclarationVisitorNoOther();
    mgr.visit(f, visitor);
    Truth.assert_()
        .withMessage(
            "declaration kind '%s' in function '%s' not available, only found '%s'.",
            expected, f, visitor.found)
        .that(visitor.found)
        .contains(expected);
  }

  @Test
  public void booleanIdVisitWithAtoms() {
    IntegerFormula n12 = imgr.makeNumber(12);
    IntegerFormula a = imgr.makeVariable("a");
    IntegerFormula b = imgr.makeVariable("b");
    IntegerFormula sum = imgr.add(a, b);
    IntegerFormula diff = imgr.subtract(a, b);
    IntegerFormula neg = imgr.negate(a);
    BooleanFormula eq = imgr.equal(n12, a);
    IntegerFormula ite = bmgr.ifThenElse(eq, sum, diff);

    for (IntegerFormula f : ImmutableList.of(a, b, n12, neg, ite)) {
      BooleanFormulaVisitor<BooleanFormula> identityVisitor =
          new BooleanFormulaTransformationVisitor(mgr) {};
      BooleanFormula bf = imgr.equal(n12, f);
      assertThatFormula(bmgr.visit(bf, identityVisitor)).isEqualTo(bf);
    }
  }

  /**
   * A very basic test for the formula visitor, defines a visitor which gathers all found free
   * variables.
   */
  @Test
  public void testFormulaVisitor() {
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");

    BooleanFormula f = bmgr.or(imgr.equal(z, imgr.add(x, y)), imgr.equal(x, imgr.add(z, y)));

    final Set<String> usedVariables = new HashSet<>();

    FormulaVisitor<TraversalProcess> nameExtractor =
        new DefaultFormulaVisitor<>() {
          @Override
          protected TraversalProcess visitDefault(Formula formula) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitFreeVariable(Formula formula, String name) {
            usedVariables.add(name);
            return TraversalProcess.CONTINUE;
          }
        };
    mgr.visitRecursively(f, nameExtractor);
    assertThat(usedVariables).containsExactly("x", "y", "z");
  }

  @Test
  public void testBooleanFormulaQuantifierHandling() throws Exception {
    requireQuantifiers();
    assume()
        .withMessage("Princess does not support quantifier over boolean variables")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    BooleanFormula x = bmgr.makeVariable("x");
    BooleanFormula constraint = qmgr.forall(ImmutableList.of(x), x);
    assertThatFormula(constraint).isUnsatisfiable();
    BooleanFormula newConstraint =
        bmgr.visit(constraint, new BooleanFormulaTransformationVisitor(mgr) {});
    assertThatFormula(newConstraint).isUnsatisfiable();
  }

  @Test
  public void testBooleanFormulaQuantifierRecursiveHandling() throws Exception {
    requireQuantifiers();
    assume()
        .withMessage("Princess does not support quantifier over boolean variables")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    BooleanFormula x = bmgr.makeVariable("x");
    BooleanFormula constraint = qmgr.forall(ImmutableList.of(x), x);
    assertThatFormula(constraint).isUnsatisfiable();
    BooleanFormula newConstraint =
        bmgr.transformRecursively(constraint, new BooleanFormulaTransformationVisitor(mgr) {});
    assertThatFormula(newConstraint).isUnsatisfiable();
  }

  // Same as testBooleanFormulaQuantifierHandling but with Ints
  @Test
  public void testIntegerFormulaQuantifierHandlingUNSAT() throws Exception {
    requireQuantifiers();
    requireIntegers();

    IntegerFormula x = imgr.makeVariable("x");
    BooleanFormula xEq1 = bmgr.not(imgr.equal(imgr.makeNumber(1), x));
    BooleanFormula constraint = qmgr.forall(ImmutableList.of(x), xEq1);
    assertThatFormula(constraint).isUnsatisfiable();
    BooleanFormula newConstraint =
        bmgr.visit(constraint, new BooleanFormulaTransformationVisitor(mgr) {});
    assertThatFormula(newConstraint).isUnsatisfiable();
  }

  @Test
  public void testIntegerFormulaQuantifierHandlingTrivialSAT() throws Exception {
    requireQuantifiers();
    requireIntegers();

    IntegerFormula x = imgr.makeVariable("x");
    BooleanFormula xEqx = imgr.equal(x, x);
    BooleanFormula constraint = qmgr.forall(ImmutableList.of(x), xEqx);
    assertThatFormula(constraint).isSatisfiable();
    BooleanFormula newConstraint =
        bmgr.visit(constraint, new BooleanFormulaTransformationVisitor(mgr) {});
    assertThatFormula(newConstraint).isSatisfiable();
  }

  @Test
  public void testIntegerFormulaQuantifierSymbolsExtraction() {
    requireQuantifiers();
    requireIntegers();

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    BooleanFormula xEqy = imgr.equal(x, y);
    // (x=y) && EX x: (X=y)
    BooleanFormula constraint = bmgr.and(xEqy, qmgr.forall(ImmutableList.of(x), xEqy));

    // The variable extraction should visit "x" and "y" only once,
    // otherwise AbstractFormulaManager#extractVariables might throw an exception,
    // when building an ImmutableMap.
    Map<String, Formula> vars = mgr.extractVariables(constraint);
    assertThat(vars).hasSize(2);
    assertThat(vars).containsEntry(x.toString(), x);
    assertThat(vars).containsEntry(y.toString(), y);
    Map<String, Formula> varsAndUfs = mgr.extractVariablesAndUFs(constraint);
    assertThat(varsAndUfs).hasSize(2);
    assertThat(varsAndUfs).containsEntry(x.toString(), x);
    assertThat(varsAndUfs).containsEntry(y.toString(), y);
  }

  @Test
  public void testIntegerFormulaQuantifierHandlingTrivialUNSAT() throws Exception {
    requireQuantifiers();
    requireIntegers();

    IntegerFormula x = imgr.makeVariable("x");
    BooleanFormula notxEqx = bmgr.not(imgr.equal(x, x));
    BooleanFormula constraint = qmgr.forall(ImmutableList.of(x), notxEqx);
    assertThatFormula(constraint).isUnsatisfiable();
    BooleanFormula newConstraint =
        bmgr.visit(constraint, new BooleanFormulaTransformationVisitor(mgr) {});
    assertThatFormula(newConstraint).isUnsatisfiable();
  }

  // The idea is to test quantifier (with bound variables),
  // such that they might fail to reconstruct the bound vars properly.
  // One of such failures may occur when the inner variables are substituted with outer vars.
  // exists x . ( forall x . (x = 1))
  // This is UNSAT as exists x_1 . ( forall x_2 . ( x_2 = 1 )).
  // If however the bound var x is inproperly substituted this might happen:
  // exists x_1 . ( forall x_2 . ( x_1 = 1 )) which is SAT
  @Test
  public void testNestedIntegerFormulaQuantifierHandling() throws Exception {
    requireQuantifiers();
    requireIntegers();
    // Z3 returns UNKNOWN as its quantifiers can not handle this.
    assume().that(solverToUse()).isNotEqualTo(Solvers.Z3);

    IntegerFormula x = imgr.makeVariable("x");
    BooleanFormula xEq1 = imgr.equal(x, imgr.makeNumber(1));
    BooleanFormula constraint =
        qmgr.exists(ImmutableList.of(x), qmgr.forall(ImmutableList.of(x), xEq1));
    assertThatFormula(constraint).isUnsatisfiable();
    BooleanFormula newConstraint =
        bmgr.visit(constraint, new BooleanFormulaTransformationVisitor(mgr) {});
    assertThatFormula(newConstraint).isUnsatisfiable();
  }

  // Same as testNestedIntegerFormulaQuantifierHandling but with a recursive visitor
  @Test
  public void testNestedIntegerFormulaQuantifierRecursiveHandling() throws Exception {
    requireQuantifiers();
    requireIntegers();
    // Z3 returns UNKNOWN as its quantifiers can not handle this.
    assume().that(solverToUse()).isNotEqualTo(Solvers.Z3);

    IntegerFormula x = imgr.makeVariable("x");
    BooleanFormula xEq1 = imgr.equal(x, imgr.makeNumber(1));
    BooleanFormula constraint =
        qmgr.exists(ImmutableList.of(x), qmgr.forall(ImmutableList.of(x), xEq1));
    assertThatFormula(constraint).isUnsatisfiable();
    BooleanFormula newConstraint =
        bmgr.transformRecursively(constraint, new BooleanFormulaTransformationVisitor(mgr) {});
    assertThatFormula(newConstraint).isUnsatisfiable();
  }

  @Test
  public void testVisitingTrue() {

    // Check that "true" is correctly treated as a constant.
    BooleanFormula t = bmgr.makeBoolean(true);
    final List<Boolean> containsTrue = new ArrayList<>();
    mgr.visitRecursively(
        t,
        new DefaultFormulaVisitor<>() {
          @Override
          protected TraversalProcess visitDefault(Formula f) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitConstant(Formula f, Object o) {
            if (f.equals(bmgr.makeBoolean(true))) {
              containsTrue.add(true);
            }
            return TraversalProcess.CONTINUE;
          }
        });
    assertThat(containsTrue).isNotEmpty();
  }

  @Test
  public void testCorrectFunctionNames() {
    BooleanFormula a = bmgr.makeVariable("a");
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula ab = bmgr.and(a, b);

    final Set<String> found = new HashSet<>();
    mgr.visitRecursively(
        ab,
        new DefaultFormulaVisitor<>() {

          @Override
          protected TraversalProcess visitDefault(Formula f) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitFunction(
              Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {

            found.add(functionDeclaration.getName());

            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitFreeVariable(Formula f, String name) {
            found.add(name);
            return TraversalProcess.CONTINUE;
          }
        });

    assertThat(found).containsAtLeast("a", "b");
    assertThat(found).hasSize(3); // all the above plus the boolean "and" function
    assertThat(found).doesNotContain(ab.toString());
  }

  @Test
  public void recursiveTransformationVisitorTest() throws Exception {
    BooleanFormula f =
        bmgr.or(
            imgr.equal(
                imgr.add(imgr.makeVariable("x"), imgr.makeVariable("y")), imgr.makeNumber(1)),
            imgr.equal(imgr.makeVariable("z"), imgr.makeNumber(10)));
    BooleanFormula transformed =
        mgr.transformRecursively(
            f,
            new FormulaTransformationVisitor(mgr) {
              @Override
              public Formula visitFreeVariable(Formula formula, String name) {
                return mgr.makeVariable(mgr.getFormulaType(formula), name + "'");
              }
            });
    assertThatFormula(transformed)
        .isEquivalentTo(
            bmgr.or(
                imgr.equal(
                    imgr.add(imgr.makeVariable("x'"), imgr.makeVariable("y'")), imgr.makeNumber(1)),
                imgr.equal(imgr.makeVariable("z'"), imgr.makeNumber(10))));
  }

  @Test
  public void recursiveTransformationVisitorTest2() throws Exception {
    BooleanFormula f = imgr.equal(imgr.makeVariable("y"), imgr.makeNumber(1));
    BooleanFormula transformed =
        mgr.transformRecursively(
            f,
            new FormulaTransformationVisitor(mgr) {
              @Override
              public Formula visitFreeVariable(Formula formula, String name) {
                return mgr.makeVariable(mgr.getFormulaType(formula), name + "'");
              }
            });
    assertThatFormula(transformed)
        .isEquivalentTo(imgr.equal(imgr.makeVariable("y'"), imgr.makeNumber(1)));
  }

  @Test
  public void booleanRecursiveTraversalTest() {
    BooleanFormula f =
        bmgr.or(
            bmgr.and(bmgr.makeVariable("x"), bmgr.makeVariable("y")),
            bmgr.and(
                bmgr.makeVariable("z"),
                bmgr.makeVariable("d"),
                imgr.equal(imgr.makeVariable("gg"), imgr.makeNumber(5))));
    final Set<String> foundVars = new HashSet<>();
    bmgr.visitRecursively(
        f,
        new DefaultBooleanFormulaVisitor<>() {
          @Override
          protected TraversalProcess visitDefault() {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitAtom(
              BooleanFormula atom, FunctionDeclaration<BooleanFormula> funcDecl) {
            if (funcDecl.getKind() == FunctionDeclarationKind.VAR) {
              foundVars.add(funcDecl.getName());
            }
            return TraversalProcess.CONTINUE;
          }
        });
    assertThat(foundVars).containsExactly("x", "y", "z", "d");
  }

  @Test
  public void testTransformationInsideQuantifiers() {
    requireQuantifiers();
    // TODO Maybe rewrite using quantified integer variable to allow testing with Princess
    assume()
        .withMessage("Princess does not support quantifier over boolean variables")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    BooleanFormula[] usedVars =
        Stream.of("a", "b", "c", "d", "e", "f")
            .map(var -> bmgr.makeVariable(var))
            .toArray(BooleanFormula[]::new);
    Fuzzer fuzzer = new Fuzzer(mgr, new Random(0));
    List<BooleanFormula> quantifiedVars = ImmutableList.of(bmgr.makeVariable("a"));
    BooleanFormula body = fuzzer.fuzz(30, usedVars);
    BooleanFormula f = qmgr.forall(quantifiedVars, body);
    BooleanFormula transformed =
        bmgr.transformRecursively(
            f,
            new BooleanFormulaTransformationVisitor(mgr) {
              @Override
              public BooleanFormula visitAtom(
                  BooleanFormula pAtom, FunctionDeclaration<BooleanFormula> decl) {
                if (decl.getKind() == FunctionDeclarationKind.VAR) {
                  // Uppercase all variables.
                  return bmgr.makeVariable(decl.getName().toUpperCase(Locale.getDefault()));
                } else {
                  return pAtom;
                }
              }
            });
    assertThat(
            mgr.extractVariables(transformed).keySet().stream()
                .allMatch(pS -> pS.equals(pS.toUpperCase(Locale.getDefault()))))
        .isTrue();
  }

  @Test
  public void testTransformationInsideQuantifiersWithTrue()
      throws SolverException, InterruptedException {
    requireQuantifiers();
    List<IntegerFormula> quantifiedVars = ImmutableList.of(imgr.makeVariable("x"));
    BooleanFormula body = bmgr.makeTrue();
    BooleanFormula f = qmgr.exists(quantifiedVars, body);
    BooleanFormula transformed = qmgr.eliminateQuantifiers(f);
    assertThat(mgr.extractVariablesAndUFs(transformed)).isEmpty();
    assertThatFormula(transformed).isEquivalentTo(body);
  }

  @Test
  public void testTransformationInsideQuantifiersWithFalse()
      throws SolverException, InterruptedException {
    requireQuantifiers();
    List<IntegerFormula> quantifiedVars = ImmutableList.of(imgr.makeVariable("x"));
    BooleanFormula body = bmgr.makeFalse();
    BooleanFormula f = qmgr.exists(quantifiedVars, body);
    BooleanFormula transformed = qmgr.eliminateQuantifiers(f);
    assertThat(mgr.extractVariablesAndUFs(transformed)).isEmpty();
    assertThatFormula(transformed).isEquivalentTo(body);
  }

  @Test
  public void testTransformationInsideQuantifiersWithVariable()
      throws SolverException, InterruptedException {
    requireQuantifiers();
    List<IntegerFormula> quantifiedVars = ImmutableList.of(imgr.makeVariable("x"));
    BooleanFormula body = bmgr.makeVariable("b");
    BooleanFormula f = qmgr.exists(quantifiedVars, body);
    BooleanFormula transformed = qmgr.eliminateQuantifiers(f);
    assertThat(mgr.extractVariablesAndUFs(transformed)).containsEntry("b", body);
    assertThatFormula(transformed).isEquivalentTo(body);
  }

  @Test
  public void extractionTest1() {
    IntegerFormula v = imgr.makeVariable("v");
    BooleanFormula q = fmgr.declareAndCallUF("q", FormulaType.BooleanType, v);
    Map<String, Formula> mapping = mgr.extractVariablesAndUFs(q);
    assertThat(mapping).hasSize(2);
    assertThat(mapping).containsEntry("v", v);
    assertThat(mapping).containsEntry("q", q);
  }

  @Test
  public void extractionTest2() {
    // the same as above, but with nullary UF.
    IntegerFormula v = fmgr.declareAndCallUF("v", FormulaType.IntegerType);
    BooleanFormula q = fmgr.declareAndCallUF("q", FormulaType.BooleanType, v);
    Map<String, Formula> mapping = mgr.extractVariablesAndUFs(q);
    Map<String, Formula> mapping2 = mgr.extractVariables(q);

    // all solvers must provide all symbols
    assertThat(mapping).hasSize(2);
    assertThat(mapping).containsEntry("v", v);
    assertThat(mapping).containsEntry("q", q);

    // some solvers distinguish between nullary UFs and variables and do not provide variables
    if (ImmutableList.of(Solvers.CVC4, Solvers.PRINCESS).contains(solverToUse())) {
      assertThat(mapping2).isEmpty();
    } else {
      assertThat(mapping2).hasSize(1);
      assertThat(mapping2).containsEntry("v", v);
    }
  }

  private final FormulaVisitor<Formula> plainFunctionVisitor =
      new DefaultFormulaVisitor<>() {

        @Override
        public Formula visitFunction(
            Formula pF, List<Formula> args, FunctionDeclaration<?> pFunctionDeclaration) {
          return fmgr.callUF(pFunctionDeclaration, args);
        }

        @Override
        protected Formula visitDefault(Formula pF) {
          return pF;
        }
      };

  @Test
  public void visitBooleanOperationWithMoreArgsTest() throws SolverException, InterruptedException {
    BooleanFormula u = bmgr.makeVariable("u");
    BooleanFormula v = bmgr.makeVariable("v");
    BooleanFormula w = bmgr.makeVariable("w");
    BooleanFormula fAnd = bmgr.and(u, v, w);
    BooleanFormula fOr = bmgr.or(u, v, w);

    Formula transformedAnd = mgr.visit(fAnd, plainFunctionVisitor);
    assertThatFormula((BooleanFormula) transformedAnd).isEquisatisfiableTo(fAnd);

    Formula transformedOr = mgr.visit(fOr, plainFunctionVisitor);
    assertThatFormula((BooleanFormula) transformedOr).isEquisatisfiableTo(fOr);
  }

  @Test
  public void visitArithmeticOperationWithMoreArgsTest()
      throws SolverException, InterruptedException {
    requireIntegers();
    requireParser();

    // INFO: OpenSMT does not support mixed integer-real logic. So we changed the types of bb and
    // cc.
    String abc =
        "(declare-fun aa () Int) (declare-fun bb () Int)"
            + "(declare-fun cc () Int) (declare-fun dd () Int)";
    BooleanFormula sum = mgr.parse(abc + "(assert (= 0 (+ aa bb cc dd)))");
    BooleanFormula equals = mgr.parse(abc + "(assert (= aa bb cc dd))");
    BooleanFormula distinct = mgr.parse(abc + "(assert (distinct aa bb cc dd))");
    BooleanFormula less = mgr.parse(abc + "(assert (< aa bb cc dd))");
    BooleanFormula lessEquals = mgr.parse(abc + "(assert (<= aa bb cc dd))");
    BooleanFormula greater = mgr.parse(abc + "(assert (> aa bb cc dd))");
    BooleanFormula greaterEquals = mgr.parse(abc + "(assert (>= aa bb cc dd))");

    for (BooleanFormula bf :
        ImmutableList.of(sum, equals, distinct, less, lessEquals, greater, greaterEquals)) {
      Formula transformed = mgr.visit(bf, plainFunctionVisitor);
      assertThatFormula((BooleanFormula) transformed).isEquisatisfiableTo(bf);
    }
  }

  @Test
  public void extractionArguments() {
    requireIntegers();

    // Create the variables and uf
    IntegerFormula a = imgr.makeVariable("a");
    IntegerFormula b = imgr.makeVariable("b");
    IntegerFormula ab = imgr.add(a, b);
    BooleanFormula uf = fmgr.declareAndCallUF("testFunc", FormulaType.BooleanType, a, b, ab);

    FormulaVisitor<Collection<Formula>> argCollectingVisitor =
        new DefaultFormulaVisitor<>() {

          final Collection<Formula> usedArgs = new LinkedHashSet<>();

          @Override
          public Collection<Formula> visitFunction(
              Formula pF, List<Formula> args, FunctionDeclaration<?> pFunctionDeclaration) {
            usedArgs.addAll(args);
            return usedArgs;
          }

          @Override
          protected Collection<Formula> visitDefault(Formula pF) {
            return usedArgs;
          }
        };

    Collection<Formula> usedArgs = mgr.visit(uf, argCollectingVisitor);

    assertThat(usedArgs).hasSize(3);
    assertThat(usedArgs).containsExactly(a, b, ab);

    Map<String, Formula> vars = mgr.extractVariables(uf);
    assertThat(vars).hasSize(2);
    assertThat(vars.keySet()).containsExactly("a", "b");

    Map<String, Formula> varsUfs = mgr.extractVariablesAndUFs(uf);
    assertThat(varsUfs).hasSize(3);
    assertThat(varsUfs.keySet()).containsExactly("a", "b", "testFunc");
  }

  @Test
  public void extractionDeclarations() {
    requireIntegers();

    // Create the variables and uf
    IntegerFormula a = imgr.makeVariable("a");
    IntegerFormula b = imgr.makeVariable("b");
    IntegerFormula ab = imgr.add(a, b);
    BooleanFormula uf1 = fmgr.declareAndCallUF("testFunc", FormulaType.BooleanType, a, b, ab);
    BooleanFormula uf2 = fmgr.declareAndCallUF("testFunc", FormulaType.BooleanType, ab, b, a);
    BooleanFormula f = bmgr.and(uf1, uf2);

    final Collection<Formula> usedArgs = new LinkedHashSet<>();
    final List<FunctionDeclaration<?>> usedDecls = new ArrayList<>();

    FormulaVisitor<TraversalProcess> argCollectingVisitor =
        new DefaultFormulaVisitor<>() {

          @Override
          public TraversalProcess visitFunction(
              Formula pF, List<Formula> args, FunctionDeclaration<?> pFunctionDeclaration) {
            usedArgs.addAll(args);
            usedDecls.add(pFunctionDeclaration);
            return visitDefault(pF);
          }

          @Override
          protected TraversalProcess visitDefault(Formula pF) {
            return TraversalProcess.CONTINUE;
          }
        };

    mgr.visitRecursively(f, argCollectingVisitor);

    // check general stuff about variables, copied from above
    assertThat(usedArgs).hasSize(5);
    assertThat(usedArgs).containsExactly(uf1, uf2, a, b, ab);

    Map<String, Formula> vars = mgr.extractVariables(f);
    assertThat(vars).hasSize(2);
    assertThat(vars.keySet()).containsExactly("a", "b");

    Map<String, Formula> varsUfs = mgr.extractVariablesAndUFs(f);
    assertThat(varsUfs).hasSize(3);
    assertThat(varsUfs.keySet()).containsExactly("a", "b", "testFunc");

    // check correct traversal order of the functions
    assertThat(usedDecls).hasSize(4);
    assertThat(usedDecls.get(0).getKind()).isEqualTo(FunctionDeclarationKind.AND);
    assertThat(usedDecls.get(1).getName()).isEqualTo("testFunc");
    assertThat(usedDecls.get(2).getKind()).isEqualTo(FunctionDeclarationKind.ADD);
    assertThat(usedDecls.get(3).getName()).isEqualTo("testFunc");

    // check UF-equality. This check went wrong in CVC4 and was fixed.
    assertThat(usedDecls.get(1)).isEqualTo(usedDecls.get(3));
  }
}
