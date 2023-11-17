; Example that previous caused an exception in the ModReducer

(set-logic BV)
(assert (forall ((q14 (_ BitVec 9)) (q15 (_ BitVec 9)) (q16 (_ BitVec 9)) (q17 (_ BitVec 14))) (=> (= (bvnot q15) q16) (distinct q17 (bvurem (bvsub q17 q17) (bvor q17 (bvsub q17 q17)))))))
(check-sat)