; Example in which previously the bvsrem was encoded incorrectly

; (set-logic HORN)
(declare-const v0 Bool)
(declare-const v1 Bool)
(declare-const v2 Bool)
(declare-const bv_14-0 (_ BitVec 14))
(assert (forall ((q0 (_ BitVec 12)) (q1 (_ BitVec 12)) (q2 (_ BitVec 12)) (q3 (_ BitVec 12)) (q4 (_ BitVec 12)) (q5 (_ BitVec 12)) (q6 (_ BitVec 12)) (q7 (_ BitVec 12)) (q8 (_ BitVec 12)) (q9 (_ BitVec 12)) (q10 (_ BitVec 12)) (q11 (_ BitVec 12)) (q12 (_ BitVec 12)) (q13 (_ BitVec 12)) (q14 (_ BitVec 12)) (q15 (_ BitVec 12)) (q16 (_ BitVec 12)) (q17 (_ BitVec 12)) (q18 (_ BitVec 12)) (q19 (_ BitVec 12)) (q20 (_ BitVec 12)) (q21 (_ BitVec 14))) (=> (distinct q16 q2) (bvsgt (bvsrem (bvudiv q21 q21) (bvashr q21 q21)) (bvashr q21 q21)))))
(check-sat)