(set-logic QF_BV)

(set-option :produce-interpolants true)

(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))

(assert (bvuge x (_ bv3 8)))
(assert (bvule x (_ bv6 8)))
(assert (= y (bvshl (_ bv1 8) x)))
(assert (not (bvugt y (_ bv5 8))))
(check-sat)

(get-interpolants)