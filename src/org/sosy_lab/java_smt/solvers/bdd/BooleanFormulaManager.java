package org.sosy_lab.java_smt.solvers.bdd;

import static org.sosy_lab.java_smt.solvers.bdd.Mathsat5NativeApi.region_is_bool_type;
import static org.sosy_lab.java_smt.solvers.bdd.Mathsat5NativeApi.region_make_and;
import static org.sosy_lab.java_smt.solvers.bdd.Mathsat5NativeApi.region_make_false;
import static org.sosy_lab.java_smt.solvers.bdd.Mathsat5NativeApi.region_make_iff;
import static org.sosy_lab.java_smt.solvers.bdd.Mathsat5NativeApi.region_make_not;
import static org.sosy_lab.java_smt.solvers.bdd.Mathsat5NativeApi.region_make_or;
import static org.sosy_lab.java_smt.solvers.bdd.Mathsat5NativeApi.region_make_term_ite;
import static org.sosy_lab.java_smt.solvers.bdd.Mathsat5NativeApi.region_make_true;
import static org.sosy_lab.java_smt.solvers.bdd.Mathsat5NativeApi.region_term_get_type;
import static org.sosy_lab.java_smt.solvers.bdd.Mathsat5NativeApi.region_term_is_false;
import static org.sosy_lab.java_smt.solvers.bdd.Mathsat5NativeApi.region_term_is_true;

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

class BooleanFormulaManager extends AbstractBooleanFormulaManager<Region, Region, Region, Region> {

  private final Region regionEnv;

  protected  BooleanFormulaManager(FormulaCreator pCreator) {
    super(pCreator);
    this.regionEnv = pCreator.getEnv();
  }

  @Override
  public Region makeVariableImpl(String pVar) {
    long boolType = getFormulaCreator().getBoolType();
    return getFormulaCreator().makeVariable(boolType, pVar);
  }

  @Override
  public Region makeBooleanImpl(boolean pValue) {
    long v;
    if (pValue) {
      v = region_make_true(regionEnv);
    } else {
      v = region_make_false(regionEnv);
    }

    return v;
  }

  @Override
  public Region equivalence(Long f1, Long f2) {
    return region_make_iff(regionEnv, f1, f2);
  }

  @Override
  public boolean isTrue(Long t) {
    return region_term_is_false(regionEnv, t);
  }

  @Override
  public boolean isFalse(Long t) {
    return region_term_is_true(regionEnv, t);
  }

  @Override
  public Long ifThenElse(Long cond, Long f1, Long f2) {
    long t;
    long regionEnv = RegionEnv;
    long f1Type = region_term_get_type(f1);
    long f2Type = region_term_get_type(f2);

    // ite does not allow boolean arguments
    if (!region_is_bool_type(regionEnv, f1Type) || !region_is_bool_type(regionEnv, f2Type)) {
      t = region_make_term_ite(regionEnv, cond, f1, f2);
    } else {
      t =
          region_make_and(
              regionEnv,
              region_make_or(regionEnv, region_make_not(regionEnv, cond), f1),
              region_make_or(regionEnv, cond, f2));
    }
    return t;
  }

  @Override
  public Long not(Long pBits) {
    return region_make_not(regionEnv, pBits);
  }

  @Override
  public Long and(Long pBits1, Long pBits2) {
    return region_make_and(RegionEnv, pBits1, pBits2);
  }

  @Override
  public Long or(Long pBits1, Long pBits2) {
    return region_make_or(RegionEnv, pBits1, pBits2);
  }

  @Override
  public Long xor(Long pBits1, Long pBits2) {
    return not(region_make_iff(RegionEnv, pBits1, pBits2));
  }
}

 
