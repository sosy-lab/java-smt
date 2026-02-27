// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import static org.sosy_lab.java_smt.api.FloatingPointNumber.DOUBLE_PRECISION_EXPONENT_SIZE;
import static org.sosy_lab.java_smt.api.FloatingPointNumber.DOUBLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT;
import static org.sosy_lab.java_smt.api.FloatingPointNumber.SINGLE_PRECISION_EXPONENT_SIZE;
import static org.sosy_lab.java_smt.api.FloatingPointNumber.SINGLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.collect.ImmutableSet;
import com.google.errorprone.annotations.Immutable;
import java.util.List;
import java.util.Set;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;

/**
 * Type of a formula.
 *
 * @param <T> Formula class corresponding to the given formula type.
 */
@SuppressWarnings("checkstyle:constantname")
@Immutable
public abstract class FormulaType<T extends Formula> {

  private FormulaType() {}

  public boolean isArrayType() {
    return false;
  }

  public boolean isBitvectorType() {
    return false;
  }

  public boolean isBooleanType() {
    return false;
  }

  public boolean isFloatingPointType() {
    return false;
  }

  public boolean isFloatingPointRoundingModeType() {
    return false;
  }

  public boolean isNumeralType() {
    return false;
  }

  public boolean isRationalType() {
    return false;
  }

  public boolean isIntegerType() {
    return false;
  }

  public boolean isSLType() {
    return false;
  }

  public boolean isStringType() {
    return false;
  }

  public boolean isRegexType() {
    return false;
  }

  public boolean isEnumerationType() {
    return false;
  }

  @Override
  public abstract String toString();

  /** return the correctly formatted SMTLIB2 type declaration. */
  public abstract String toSMTLIBString();

  @Immutable
  public abstract static class NumeralType<T extends NumeralFormula> extends FormulaType<T> {

    @Override
    public final boolean isNumeralType() {
      return true;
    }
  }

  @SuppressWarnings("ClassInitializationDeadlock")
  public static final FormulaType<RationalFormula> RationalType =
      new NumeralType<>() {

        @Override
        public boolean isRationalType() {
          return true;
        }

        @Override
        public String toString() {
          return "Rational";
        }

        @Override
        public String toSMTLIBString() {
          return "Real";
        }
      };

  @SuppressWarnings("ClassInitializationDeadlock")
  public static final FormulaType<IntegerFormula> IntegerType =
      new NumeralType<>() {

        @Override
        public boolean isIntegerType() {
          return true;
        }

        @Override
        public String toString() {
          return "Integer";
        }

        @Override
        public String toSMTLIBString() {
          return "Int";
        }
      };

  public static final FormulaType<BooleanFormula> BooleanType =
      new FormulaType<>() {

        @Override
        public boolean isBooleanType() {
          return true;
        }

        @Override
        public String toString() {
          return "Boolean";
        }

        @Override
        public String toSMTLIBString() {
          return "Bool";
        }
      };

  public static BitvectorType getBitvectorTypeWithSize(int size) {
    return new BitvectorType(size);
  }

  @Immutable
  public static final class BitvectorType extends FormulaType<BitvectorFormula> {
    private final int size;

    private BitvectorType(int size) {
      this.size = size;
    }

    @Override
    public boolean isBitvectorType() {
      return true;
    }

    public int getSize() {
      return size;
    }

    @Override
    public String toString() {
      return "Bitvector<" + getSize() + ">";
    }

    @Override
    public boolean equals(Object pObj) {
      if (pObj == this) {
        return true;
      }
      if (!(pObj instanceof BitvectorType)) {
        return false;
      }
      BitvectorType other = (BitvectorType) pObj;
      return size == other.size;
    }

    @Override
    public int hashCode() {
      return size;
    }

    @Override
    public String toSMTLIBString() {
      return "(_ BitVec " + size + ")";
    }
  }

  /**
   * Constructs a new IEEE-754 {@link FloatingPointType} with the given exponent and mantissa sizes.
   * The mantissa size is expected to not include the hidden bit.
   *
   * @deprecated this method can be confusing, as the SMTLIB2 standard expects the mantissa to
   *     include the hidden bit, but this method expects the mantissa argument without the hidden
   *     bit. Use {@link #getFloatingPointTypeFromSizesWithoutHiddenBit(int, int)} instead if you
   *     want to construct a {@link FloatingPointType} with the constructing method treating the
   *     mantissa argument without the hidden bit, and {@link
   *     #getFloatingPointTypeFromSizesWithHiddenBit(int, int)} if you want it to include the hidden
   *     bit in the size of the mantissa argument.
   * @param exponentSize size of the exponent for the base of the floating-point
   * @param mantissaSizeWithoutHiddenBit size of the mantissa (also called a coefficient or
   *     significand), excluding the hidden bit.
   * @return the newly constructed {@link FloatingPointType}.
   */
  @Deprecated(since = "6.0", forRemoval = true)
  @SuppressWarnings("InlineMeSuggester")
  public static FloatingPointType getFloatingPointType(
      int exponentSize, int mantissaSizeWithoutHiddenBit) {
    return getFloatingPointTypeFromSizesWithoutHiddenBit(
        exponentSize, mantissaSizeWithoutHiddenBit);
  }

  /**
   * Constructs a new IEEE-754 {@link FloatingPointType} with the given exponent and mantissa sizes.
   * The mantissa size is expected to not include the hidden bit. The total size of the constructed
   * type is equal to the addition of the two arguments plus one, as in: total size == exponentSize
   * + mantissaSizeWithoutHiddenBit + 1.
   *
   * <p>Using the arguments e and m, calling this method with
   * getFloatingPointTypeFromSizesWithoutHiddenBit (e, m) returns a type equal to a type constructed
   * by {@link #getFloatingPointTypeFromSizesWithHiddenBit(int, int)} with the same arguments e and
   * m as before, but m incremented by 1, as in getFloatingPointTypeFromSizesWithHiddenBit(e, m +
   * 1).
   *
   * @param exponentSize size of the exponent for the base of the floating-point
   * @param mantissaSizeWithoutHiddenBit size of the mantissa (also called a coefficient or
   *     significand), excluding the hidden bit.
   * @return the newly constructed {@link FloatingPointType}.
   */
  public static FloatingPointType getFloatingPointTypeFromSizesWithoutHiddenBit(
      int exponentSize, int mantissaSizeWithoutHiddenBit) {
    return new FloatingPointType(exponentSize, mantissaSizeWithoutHiddenBit);
  }

  /**
   * Constructs a new IEEE-754 {@link FloatingPointType} with the given exponent and mantissa sizes.
   * The mantissa size is expected to include the hidden bit. The total size of the constructed type
   * is equal to the addition of the two arguments, as in: total size == exponentSize +
   * mantissaSizeWithHiddenBit.
   *
   * <p>Using the arguments e and m, calling this method with
   * getFloatingPointTypeFromSizesWithHiddenBit(e, m) returns a type equal to a type constructed by
   * {@link #getFloatingPointTypeFromSizesWithoutHiddenBit(int, int)} with the same arguments e and
   * m as before, but m decremented by 1, as in getFloatingPointTypeFromSizesWithoutHiddenBit(e, m -
   * 1).
   *
   * @param exponentSize size of the exponent for the base of the floating-point
   * @param mantissaSizeWithHiddenBit size of the mantissa (also called a coefficient or
   *     significand), including the hidden bit.
   * @return the newly constructed {@link FloatingPointType}.
   */
  public static FloatingPointType getFloatingPointTypeFromSizesWithHiddenBit(
      int exponentSize, int mantissaSizeWithHiddenBit) {
    return getFloatingPointTypeFromSizesWithoutHiddenBit(
        exponentSize, mantissaSizeWithHiddenBit - 1);
  }

  /**
   * @return a single precision {@link FloatingPointType} with a total size of 32 bits, consisting
   *     of the sign bit, an exponent sized 8 bits, and a mantissa sized 23 bits (excluding the
   *     hidden bit).
   */
  public static FloatingPointType getSinglePrecisionFloatingPointType() {
    return FloatingPointType.SINGLE_PRECISION_FP_TYPE;
  }

  /**
   * @return a double precision {@link FloatingPointType} with a total size of 64 bits, consisting
   *     of the sign bit, an exponent sized 11 bits, and a mantissa sized 52 bits (excluding the
   *     hidden bit).
   */
  public static FloatingPointType getDoublePrecisionFloatingPointType() {
    return FloatingPointType.DOUBLE_PRECISION_FP_TYPE;
  }

  @Immutable
  public static final class FloatingPointType extends FormulaType<FloatingPointFormula> {

    @SuppressWarnings("removal")
    private static final FloatingPointType SINGLE_PRECISION_FP_TYPE =
        new FloatingPointType(
            SINGLE_PRECISION_EXPONENT_SIZE, SINGLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT);

    @SuppressWarnings("removal")
    private static final FloatingPointType DOUBLE_PRECISION_FP_TYPE =
        new FloatingPointType(
            DOUBLE_PRECISION_EXPONENT_SIZE, DOUBLE_PRECISION_MANTISSA_SIZE_WITHOUT_HIDDEN_BIT);

    private final int exponentSize;
    // The SMTLib2 standard defines the mantissa size as including the hidden bit. We do not include
    // it here though.
    private final int mantissaSizeWithoutHiddenBit;

    private FloatingPointType(int pExponentSize, int pMantissaSizeWithoutHiddenBit) {
      exponentSize = pExponentSize;
      mantissaSizeWithoutHiddenBit = pMantissaSizeWithoutHiddenBit;
    }

    @Override
    public boolean isFloatingPointType() {
      return true;
    }

    /** Returns the size of the exponent. */
    public int getExponentSize() {
      return exponentSize;
    }

    /**
     * Returns the size of the mantissa (also called a coefficient or significand), excluding the
     * hidden bit.
     *
     * @deprecated this method can be confusing, as the SMTLIB2 standard expects the mantissa to
     *     include the hidden bit, but this does not. Use {@link #getMantissaSizeWithoutHiddenBit()}
     *     instead if you want the mantissa without the hidden bit, and {@link
     *     #getMantissaSizeWithHiddenBit()} if you want it to include the hidden bit.
     */
    @Deprecated(since = "6.0", forRemoval = true)
    public int getMantissaSize() {
      return mantissaSizeWithoutHiddenBit;
    }

    /**
     * Returns the size of the mantissa (also called a coefficient or significand), excluding the
     * hidden bit.
     */
    public int getMantissaSizeWithoutHiddenBit() {
      return mantissaSizeWithoutHiddenBit;
    }

    /**
     * Returns the size of the mantissa (also called a coefficient or significand), including the
     * hidden bit.
     */
    public int getMantissaSizeWithHiddenBit() {
      return mantissaSizeWithoutHiddenBit + 1;
    }

    /**
     * Return the total bit size of a value of this type (i.e. the precision). Defined by the <a
     * href="https://smt-lib.org/theories-FloatingPoint.shtml">SMT-LIB2 standard</a> as being equal
     * to the "size of the exponent + size of the mantissa including the hidden bit". This is equal
     * to the total size as defined by the <a
     * href="https://ieeexplore.ieee.org/document/4610935">IEEE 754-2008 floating-point
     * standard</a>, as being equal to "sign bit + size of the exponent + size of the mantissa
     * excluding the hidden bit".
     */
    public int getTotalSize() {
      return exponentSize + getMantissaSizeWithHiddenBit();
    }

    @Override
    public int hashCode() {
      return (31 + exponentSize) * 31 + mantissaSizeWithoutHiddenBit;
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj) {
        return true;
      }
      if (!(obj instanceof FloatingPointType)) {
        return false;
      }
      FloatingPointType other = (FloatingPointType) obj;
      return this.exponentSize == other.exponentSize
          && this.mantissaSizeWithoutHiddenBit == other.mantissaSizeWithoutHiddenBit;
    }

    @Override
    public String toString() {
      // We align what we do here with the SMTLIB2 standard, which expects the hidden bit to be part
      // of the mantissa.
      return "FloatingPoint<exp=" + exponentSize + ",mant=" + getMantissaSizeWithHiddenBit() + ">";
    }

    @Override
    public String toSMTLIBString() {
      return "(_ FloatingPoint " + exponentSize + " " + getMantissaSizeWithHiddenBit() + ")";
    }
  }

  public static final FormulaType<FloatingPointRoundingModeFormula> FloatingPointRoundingModeType =
      new FloatingPointRoundingModeType();

  private static final class FloatingPointRoundingModeType
      extends FormulaType<FloatingPointRoundingModeFormula> {

    @Override
    public boolean isFloatingPointRoundingModeType() {
      return true;
    }

    @Override
    public String toString() {
      return "FloatingPointRoundingMode";
    }

    @Override
    public String toSMTLIBString() {
      throw new UnsupportedOperationException(
          "rounding mode is not expected in symbol declarations");
    }
  }

  @SuppressWarnings("MethodTypeParameterName")
  public static <TD extends Formula, TR extends Formula> ArrayFormulaType<TD, TR> getArrayType(
      FormulaType<TD> pDomainSort, FormulaType<TR> pRangeSort) {
    return new ArrayFormulaType<>(pDomainSort, pRangeSort);
  }

  @SuppressWarnings("ClassTypeParameterName")
  public static final class ArrayFormulaType<TI extends Formula, TE extends Formula>
      extends FormulaType<ArrayFormula<TI, TE>> {

    private final FormulaType<TE> elementType;
    private final FormulaType<TI> indexType;

    private ArrayFormulaType(FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
      this.indexType = Preconditions.checkNotNull(pIndexType);
      this.elementType = Preconditions.checkNotNull(pElementType);
    }

    public FormulaType<TE> getElementType() {
      return elementType;
    }

    public FormulaType<TI> getIndexType() {
      return indexType;
    }

    @Override
    public boolean isArrayType() {
      return true;
    }

    @Override
    public String toString() {
      return String.format("Array<%s,%s>", indexType, elementType);
    }

    @Override
    public int hashCode() {
      return 31 * elementType.hashCode() + indexType.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj) {
        return true;
      }
      if (!(obj instanceof ArrayFormulaType)) {
        return false;
      }
      ArrayFormulaType<?, ?> other = (ArrayFormulaType<?, ?>) obj;
      return elementType.equals(other.elementType) && indexType.equals(other.indexType);
    }

    @Override
    public String toSMTLIBString() {
      return "(Array " + indexType.toSMTLIBString() + " " + elementType.toSMTLIBString() + ")";
    }
  }

  public static EnumerationFormulaType getEnumerationType(String pName, Set<String> pElements) {
    return new EnumerationFormulaType(pName, pElements);
  }

  public static final class EnumerationFormulaType extends FormulaType<EnumerationFormula> {

    private final String name;
    private final ImmutableSet<String> elements;

    private EnumerationFormulaType(String pName, Set<String> pElements) {
      this.name = Preconditions.checkNotNull(pName);
      this.elements = ImmutableSet.copyOf(pElements);
    }

    public String getName() {
      return name;
    }

    public ImmutableSet<String> getElements() {
      return elements;
    }

    public int getCardinality() {
      return elements.size();
    }

    @Override
    public boolean isEnumerationType() {
      return true;
    }

    @Override
    public String toString() {
      return String.format("%s (%s)", name, Joiner.on(", ").join(elements));
    }

    @Override
    public int hashCode() {
      return 31 * name.hashCode() + elements.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj) {
        return true;
      }
      if (!(obj instanceof EnumerationFormulaType)) {
        return false;
      }
      EnumerationFormulaType other = (EnumerationFormulaType) obj;
      return name.equals(other.name) && elements.equals(other.elements);
    }

    @Override
    public String toSMTLIBString() {
      return "(" + this + ")";
    }
  }

  public static final FormulaType<StringFormula> StringType =
      new FormulaType<>() {

        @Override
        public boolean isStringType() {
          return true;
        }

        @Override
        public String toString() {
          return "String";
        }

        @Override
        public String toSMTLIBString() {
          return "String";
        }
      };

  public static final FormulaType<RegexFormula> RegexType =
      new FormulaType<>() {

        @Override
        public boolean isRegexType() {
          return true;
        }

        @Override
        public String toString() {
          return "RegLan";
        }

        @Override
        public String toSMTLIBString() {
          return "RegLan";
        }
      };

  /**
   * Parse a string and return the corresponding type. This method is the counterpart of {@link
   * #toString()}.
   */
  public static FormulaType<?> fromString(String t) {
    if (BooleanType.toString().equals(t)) {
      return BooleanType;
    } else if (IntegerType.toString().equals(t)) {
      return IntegerType;
    } else if (RationalType.toString().equals(t)) {
      return RationalType;
    } else if (StringType.toString().equals(t)) {
      return StringType;
    } else if (RegexType.toString().equals(t)) {
      return RegexType;
    } else if (FloatingPointRoundingModeType.toString().equals(t)) {
      return FloatingPointRoundingModeType;
    } else if (t.startsWith("FloatingPoint<")) {
      // Example: FloatingPoint<exp=11,mant=52>
      List<String> exman = Splitter.on(',').limit(2).splitToList(t.substring(14, t.length() - 1));
      // We align what we do here with the SMTLIB2 standard, which expects the hidden bit to be part
      // of the mantissa.
      return FormulaType.getFloatingPointTypeFromSizesWithHiddenBit(
          Integer.parseInt(exman.get(0).substring(4)), Integer.parseInt(exman.get(1).substring(5)));
    } else if (t.startsWith("Bitvector<")) {
      // Example: Bitvector<32>
      return FormulaType.getBitvectorTypeWithSize(
          Integer.parseInt(t.substring(10, t.length() - 1)));
    } else if (t.matches(".*\\(.*\\)")) {
      // Example: Color (Red, Green, Blue)
      String name = t.substring(0, t.indexOf("(") - 1);
      String elementsStr = t.substring(t.indexOf("(") + 1, t.length() - 1);
      Set<String> elements = ImmutableSet.copyOf(Splitter.on(", ").split(elementsStr));
      return new EnumerationFormulaType(name, elements);
    } else {
      throw new AssertionError("unknown type:" + t);
    }
  }
}
