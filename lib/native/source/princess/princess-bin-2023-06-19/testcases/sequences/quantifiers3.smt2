(declare-const s (Seq Int))
(declare-const j Int)

(assert (forall ((x Int)) (>= (seq.nth s x) 0)))
(assert (<= 10 (seq.len s)))
(assert (<= 0 j))
(assert (<= j 8))
(assert (< (seq.nth s j) (- 10)))
(check-sat)

