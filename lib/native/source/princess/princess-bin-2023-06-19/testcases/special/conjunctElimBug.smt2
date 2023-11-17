; Example that previously led to an assertion failure in ConjunctEliminator

(set-logic HORN)
(declare-const v0 Bool)
(declare-const v1 Bool)
(declare-const v2 Bool)
(declare-const bv_15-0 (_ BitVec 15))
(assert (forall ((q1 (_ BitVec 9)) (q2 (_ BitVec 9)) (q3 (_ BitVec 9)) (q4 (_ BitVec 10))) (=> (= q4 q4) (= (bvnor q2 (bvsrem q1 q2)) (bvnor q2 (bvsrem q1 q2))))))
; (assert (forall ((q5 (_ BitVec 9)) (q6 (_ BitVec 9)) (q7 (_ BitVec 9)) (q8 (_ BitVec 9)) (q9 (_ BitVec 15))) (=> (= q9 q9) (distinct (bvneg q7) (bvneg q7)))))
(check-sat)
(exit)
