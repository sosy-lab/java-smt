; Example that previously led to a warning about unbounded shifts

(set-logic BV)
(assert (forall ((q3 (_ BitVec 8)) (q4 (_ BitVec 9)) (q5 (_ BitVec 8)))
    (distinct (bvlshr (bvsdiv q5 q5) (bvsdiv q5 q5)) q3)))
(check-sat)
