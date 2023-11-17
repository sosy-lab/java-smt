

(declare-const y Int)
(declare-const z Int)
(declare-const y2 Int)
(declare-const z2 Int)

(assert (= (store ((as const (Array Int Int)) y) 2 y2)
           (store ((as const (Array Int Int)) z) 2 z2)))
(assert (not (= y z)))
(check-sat)
