(set-logic QF_BV)

(declare-const x0 (_ BitVec 32))
(declare-const y0 (_ BitVec 32))

(declare-const x1 (_ BitVec 32))
(declare-const y1 (_ BitVec 32))

(assert (= x1 (bvmul x0 x0)))
(assert (= y1 (bvadd x1 (_ bv1 32))))

(assert (not (bvsgt y1 (_ bv0 32))))

(check-sat)

