(set-logic QF_BV)

(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))

(assert (= x (_ bv3 8)))
(assert (= y (bvshl (_ bv1 8) x)))
(assert (not (bvugt y (_ bv5 8))))
(check-sat)
