
package org.sosy_lab.java_smt.solvers.bdd;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_and;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_ashr;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_concat;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_extract;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_lshl;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_lshr;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_minus;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_neg;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_not;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_or;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_plus;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_sdiv;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_sext;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_sleq;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_slt;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_srem;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_times;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_udiv;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_uleq;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_ult;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_urem;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_xor;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_zext;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_equal;

import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

/** Mathsat Bitvector Theory, build out of Bitvector*Operations. */
class BitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Region, Region, Region, Region> {

  private final Region regionEnv;

  protected BitvectorFormulaManager(FormulaCreator pCreator) {
    super(pCreator);
    this.regionEnv = pCreator.getEnv();
  }

  public static BitvectorFormulaManager create(regionCreator creator) {
    return new BitvectorFormulaManager(creator);
  }

  @Override
  public Long concat(Region pFirst, Region pSecond) {
    return region_make_bv_concat(regionEnv, pFirst, pSecond);
  }

  @Override
  public Region extract(Region pFirst, int pMsb, int pLsb, boolean pSigned) {
    return region_make_bv_extract(regionEnv, pMsb, pLsb, pFirst);
  }

  @Override
  public Long extend(Long pNumber, int pExtensionBits, boolean pSigned) {
    if (pSigned) {
      return region_make_bv_sext(regionEnv, pExtensionBits, pNumber);
    } else {
      return region_make_bv_zext(regionEnv, pExtensionBits, pNumber);
    }
  }

  @Override
  public Long makeBitvectorImpl(int pLength, long pI) {
    int i = (int) pI;
    if (i == pI && i > 0) { // fits into an int
      return Mathsat5NativeApi.msat_make_bv_int_number(mathsatEnv, i, pLength);
    }
    return makeBitvectorImpl(pLength, BigInteger.valueOf(pI));
  }

  @Override
  public Long makeBitvectorImpl(int pLength, BigInteger pI) {
    if (pI.signum() < 0) {
      BigInteger max = BigInteger.valueOf(2).pow(pLength - 1);
      if (pI.compareTo(max.negate()) < 0) {
        throw new IllegalArgumentException(
            pI + " is to small for a bitvector with length " + pLength);
      }
      BigInteger n = BigInteger.valueOf(2).pow(pLength);
      pI = pI.add(n);
    }
    return msat_make_bv_number(mathsatEnv, pI.toString(), pLength, 10);
  }

  @Override
  public Region makeVariableImpl(Region length, String var) {
    Region bvType = getFormulaCreator().getBitvectorType(length);
    return getFormulaCreator().makeVariable(bvType, var);
  }

  /**
   * Return a term representing the (arithmetic if signed is true) right shift of number by toShift.
   */
  @Override
  public Region shiftRight(Region number, Region toShift, boolean signed) {
    long t;
    if (signed) {
      t = region_make_bv_ashr(regionEnv, number, toShift);
    } else {
      t = region_make_bv_lshr(regionEnv, number, toShift);
    }
    return t;
  }

  @Override
  public Long shiftLeft(Long number, Long toShift) {
    return msat_make_bv_lshl(mathsatEnv, number, toShift);
  }

  @Override
  public Region not(Region pBits) {
    return region_make_bv_not(regionEnv, pBits);
  }

  @Override
  public Region and(Region pBits1, Region pBits2) {
    return region_make_bv_and(mathsatEnv, pBits1, pBits2);
  }

  @Override
  public Long or(Long pBits1, Long pBits2) {
    return msat_make_bv_or(mathsatEnv, pBits1, pBits2);
  }

  @Override
  public Long xor(Long pBits1, Long pBits2) {
    return msat_make_bv_xor(mathsatEnv, pBits1, pBits2);
  }

  @Override
  public Long negate(Long pNumber) {
    return msat_make_bv_neg(mathsatEnv, pNumber);
  }

  @Override
  public Long add(Long pNumber1, Long pNumber2) {
    return msat_make_bv_plus(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  public Long subtract(Long pNumber1, Long pNumber2) {
    return msat_make_bv_minus(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  public Long divide(Long pNumber1, Long pNumber2, boolean signed) {
    if (signed) {
      return msat_make_bv_sdiv(mathsatEnv, pNumber1, pNumber2);
    } else {
      return msat_make_bv_udiv(mathsatEnv, pNumber1, pNumber2);
    }
  }

  @Override
  public Long modulo(Long pNumber1, Long pNumber2, boolean signed) {
    if (signed) {
      return msat_make_bv_srem(mathsatEnv, pNumber1, pNumber2);
    } else {
      return msat_make_bv_urem(mathsatEnv, pNumber1, pNumber2);
    }
  }

  @Override
  public Long multiply(Long pNumber1, Long pNumber2) {
    return msat_make_bv_times(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  public Long equal(Long pNumber1, Long pNumber2) {
    return msat_make_equal(mathsatEnv, pNumber1, pNumber2);
  }

  @Override
  public Long lessThan(Long pNumber1, Long pNumber2, boolean signed) {
    if (signed) {
      return msat_make_bv_slt(mathsatEnv, pNumber1, pNumber2);
    } else {
      return msat_make_bv_ult(mathsatEnv, pNumber1, pNumber2);
    }
  }

  @Override
  public Long lessOrEquals(Long pNumber1, Long pNumber2, boolean signed) {
    if (signed) {
      return msat_make_bv_sleq(mathsatEnv, pNumber1, pNumber2);
    } else {
      return msat_make_bv_uleq(mathsatEnv, pNumber1, pNumber2);
    }
  }

  @Override
  public Long greaterThan(Long pNumber1, Long pNumber2, boolean signed) {
    return lessThan(pNumber2, pNumber1, signed);
  }

  @Override
  public Long greaterOrEquals(Long pNumber1, Long pNumber2, boolean signed) {
    return lessOrEquals(pNumber2, pNumber1, signed);
  }
}


