; Example that previously gave unsat, incorrectly

(set-logic QF_BV)

(declare-fun r1 () (_ BitVec 8))
(declare-fun r2 () (_ BitVec 8))
(declare-fun r3 () (_ BitVec 8))
(declare-fun r4 () (_ BitVec 8))
(assert (= (bvsdiv (_ bv10 8) (_ bv3 8)) r1))
(assert (= (bvsdiv (_ bv10 8) (_ bv253 8)) r2))
(assert (= (bvsdiv (_ bv246 8) (_ bv3 8)) r3))
(assert (= (bvsdiv (_ bv246 8) (_ bv253 8)) r4))

(check-sat)
(get-model)
