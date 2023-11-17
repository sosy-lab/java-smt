
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))

(assert (= x y))
(assert (bvult (bvcomp x y) (_ bv1 1)))

(check-sat)
