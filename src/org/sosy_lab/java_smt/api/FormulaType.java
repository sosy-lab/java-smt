// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import static org.sosy_lab.java_smt.api.FloatingPointNumber.DOUBLE_PRECISION_EXPONENT_SIZE;
import static org.sosy_lab.java_smt.api.FloatingPointNumber.DOUBLE_PRECISION_MANTISSA_SIZE;
import static org.sosy_lab.java_smt.api.FloatingPointNumber.SINGLE_PRECISION_EXPONENT_SIZE;
import static org.sosy_lab.java_smt.api.FloatingPointNumber.SINGLE_PRECISION_MANTISSA_SIZE;

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

  public static FloatingPointType getFloatingPointType(int exponentSize, int mantissaSize) {
    return new FloatingPointType(exponentSize, mantissaSize);
  }

  public static FloatingPointType getSinglePrecisionFloatingPointType() {
    return FloatingPointType.SINGLE_PRECISION_FP_TYPE;
  }

  public static FloatingPointType getDoublePrecisionFloatingPointType() {
    return FloatingPointType.DOUBLE_PRECISION_FP_TYPE;
  }

  @Immutable
  public static final class FloatingPointType extends FormulaType<FloatingPointFormula> {

    private static final FloatingPointType SINGLE_PRECISION_FP_TYPE =
        new FloatingPointType(SINGLE_PRECISION_EXPONENT_SIZE, SINGLE_PRECISION_MANTISSA_SIZE);
    private static final FloatingPointType DOUBLE_PRECISION_FP_TYPE =
        new FloatingPointType(DOUBLE_PRECISION_EXPONENT_SIZE, DOUBLE_PRECISION_MANTISSA_SIZE);

    private final int exponentSize;
    private final int mantissaSize;

    private FloatingPointType(int pExponentSize, int pMantissaSize) {
      exponentSize = pExponentSize;
      mantissaSize = pMantissaSize;
    }

    @Override
    public boolean isFloatingPointType() {
      return true;
    }

    public int getExponentSize() {
      return exponentSize;
    }

    public int getMantissaSize() {
      return mantissaSize;
    }

    /** Return the total size of a value of this type in bits. */
    public int getTotalSize() {
      return exponentSize + mantissaSize + 1;
    }

    @Override
    public int hashCode() {
      return (31 + exponentSize) * 31 + mantissaSize;
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
      return this.exponentSize == other.exponentSize && this.mantissaSize == other.mantissaSize;
    }

    @Override
    public String toString() {
      return "FloatingPoint<exp=" + exponentSize + ",mant=" + mantissaSize + ">";
    }

    @Override
    public String toSMTLIBString() {
      return "(_ FloatingPoint " + exponentSize + " " + mantissaSize + ")";
    }
  }

  public static final FormulaType<FloatingPointRoundingModeFormula> FloatingPointRoundingModeType =
      new FloatingPointRoundingModeType();

  private static class FloatingPointRoundingModeType
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
      // FloatingPoint<exp=11,mant=52>
      List<String> exman = Splitter.on(',').limit(2).splitToList(t.substring(14, t.length() - 1));
      return FormulaType.getFloatingPointType(
          Integer.parseInt(exman.get(0).substring(4)), Integer.parseInt(exman.get(1).substring(5)));
    } else if (t.startsWith("Bitvector<")) {
      // Bitvector<32>
      return FormulaType.getBitvectorTypeWithSize(
          Integer.parseInt(t.substring(10, t.length() - 1)));
    } else if (t.matches(".*\\(.*\\)")) {
      // Color (Red, Green, Blue)
      String name = t.substring(0, t.indexOf("(") - 1);
      String elementsStr = t.substring(t.indexOf("(") + 1, t.length() - 1);
      Set<String> elements = ImmutableSet.copyOf(Splitter.on(", ").split(elementsStr));
      return new EnumerationFormulaType(name, elements);
    } else {
      throw new AssertionError("unknown type:" + t);
    }
  }
}
