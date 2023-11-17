

(declare-const ar (Array Int Int))
(declare-const y Int)
(declare-const z Int)
(declare-const y2 Int)
(declare-const z2 Int)

(assert (= (store (store ar 1 y) 2 y2)
           (store (store ar 1 z) 2 z2)))
(assert (not (= y z)))
(check-sat)
