
package org.sosy_lab.java_smt.solvers.bdd;

import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

class BddBitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Region, Sort, Context, funcDecl> {

  public static native Region sleq(Region e, Region t1, Region t2);

  public static native Region next(Region e, Region t1, Region t2);

  public static native Region sext(Region e, Region t1, Region t2);

  public static native Region extract(Region e, Region t1, Region t2);

  public static native Region concat(Region e, Region t1, Region t2);

  public static native Region times(Region e, Region t1, Region t2);

  public static native Region smod(Region e, Region t1, Region t2);

  public static native Region umod(Region e, Region t1, Region t2);

  public static native Region neg(Region e, Region t1);

  public static native Region minus(Region e, Region t1, Region t2);

  public static native Region uleq(Region e, Region t1, Region t2);

  public static native Region slt(Region e, Region t1, Region t2);

  public static native Region ult(Region e, Region t1, Region t2);

  public static native Region equal(Region e, Region t1, Region t2);

  public static native Region plus(Region e, Region t1, Region t2);

  public static native Region sdiv(Region e, Region t1, Region t2);

  public static native Region udiv(Region e, Region t1, Region t2);

  public static native Region xor(Region e, Region t1, Region t2);

  public static native Region or(Region e, Region t1, Region t2);


  public static native Region sl(Region e, Region t1, Region t2);

  public static native Region signedsr(Region e, Region t1, Region t2);

  public static native Region usignedsr(Region e, Region t1, Region t2);

  public static native Region not(Region e, Region t1);

  private final Region region;

  protected BddBitvectorFormulaManager(BddFormulaCreator pCreator) {
    super(pCreator);
    this.region = pCreator.getEnv();
  }

  public static BddBitvectorFormulaManager create(BddFormulaCreator creator) {
    return new BddBitvectorFormulaManager(creator);
  }

  @Override
  public Region concat(Region pFirst, Region pSecond) {
    return concat(region, pFirst, pSecond);
  }

  @Override
  public Region extract(Region pFirst, int pMsb, int pLsb, boolean pSigned) {
    return extract(region, pMsb, pLsb, pFirst);
  }

  @Override
  public Long extend(Long pNumber, int pExtensionBits, boolean pSigned) {
    if (pSigned) {
      return uext(region, pExtensionBits, pNumber);
    } else {
      return sext(region, pExtensionBits, pNumber);
    }
  }

  @Override
  public Long makeBitvectorImpl(int pLength, long pI) {
    return null;
  }

  @Override
  public Long makeBitvectorImpl(int pLength, BigInteger pI) {
    return null;
  }

  @Override
  public Long makeVariableImpl(int length, String var) {
    return null;
  }


  @Override
  public Long shiftRight(Long number, Long toShift, boolean signed) {
    Region t;
    if (signed) {
      t = signedsr(region, number, toShift);
    } else {
      t = usignedsr(region, number, toShift);
    }
    return t;
  }


  @Override
  public Long shiftLeft(Long number, Long toShift) {
    return sl(region, number, toShift);
  }

  @Override
  public Region not(Region pBits) {
    return not(region, pBits);
  }

  @Override
  public Region and(Region pBits1, Region pBits2) {
    return and(region, pBits1, pBits2);
  }

  @Override
  public Region or(Region pBits1, Region pBits2) {
    return or(region, pBits1, pBits2);
  }

  @Override
  public Region xor(Region pBits1, Region pBits2) {
    return xor(region, pBits1, pBits2);
  }

  @Override
  public Region negate(Region pNumber) {
    return neg(region, pNumber);
  }

  @Override
  public Region add(Long pNumber1, Long pNumber2) {
    return plus(region, pNumber1, pNumber2);

  }

  @Override
  public Region subtract(Region pNumber1, Region pNumber2) {
    return minus(region, pNumber1, pNumber2);
  }

  @Override
  public Region divide(Region pNumber1, Region pNumber2, boolean signed) {
    if (signed) {
      return sdiv(region, pNumber1, pNumber2);
    } else {
      return udiv(region, pNumber1, pNumber2);
    }


  }

  @Override
  public Region modulo(Region pNumber1, Region pNumber2, boolean signed) {
    if (signed) {
      return smod(region, pNumber1, pNumber2);
    } else {
      return umod(region, pNumber1, pNumber2);
    }

  }

  @Override
  public Region multiply(Region pNumber1, Region pNumber2) {
    return times(region, pNumber1, pNumber2);
  }

  @Override
  public Region equal(Region pNumber1, Region pNumber2) {
    // pNumber1.equals(pNumber2);
    return equal(region, pNumber1, pNumber2);
  }

  @Override
  public Region lessThan(Region pNumber1, Region pNumber2, boolean signed) {
    if(signed){
      return slt(region, pNumber1, pNumber2);
    }else {
      return ult(region, pNumber1, pNumber2);
  }
  }

  @Override
  public Region lessOrEquals(Region pNumber1, Region pNumber2, boolean signed) {
    if (signed) {
      return sleq(region, pNumber1, pNumber2);
    } else {
      return uleq(region, pNumber1, pNumber2);

    }
  }

  @Override
  public Region greaterThan(Region pNumber1, Region pNumber2, boolean signed) {
    return lessThan(pNumber2, pNumber1, signed);
  }

  @Override
  public Region greaterOrEquals(Region pNumber1, Region pNumber2, boolean signed) {
    return lessOrEquals(pNumber2, pNumber1, signed);
  }
}
