(declare-const s (Array Int Int))
(declare-const j Int)

(assert (forall ((x Int)) (>= (select s x) 0)))
(assert (< (select s j) (- 10)))
(check-sat)

