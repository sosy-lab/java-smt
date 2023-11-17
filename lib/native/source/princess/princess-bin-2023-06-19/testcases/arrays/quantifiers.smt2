; Example for which the prover should report "unknown", since the
; constructed model does not satisfy the quantified axiom.

(declare-const a (Array Int Int))

(assert (forall ((x Int)) (= (select a x) x)))
(assert (= (select a 0) 0))

(check-sat)
