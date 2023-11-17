

(declare-const ar (Array Int Int))
(declare-const ar2 (Array Int Int))
(declare-const ar3 (Array Int Int))
(declare-const y Int)
(declare-const z Int)
(declare-const y2 Int)
(declare-const z2 Int)

(assert (= ar2 (store ar 1 y)))
(assert (= ar (store ar2 1 z)))

(assert (not (= y z)))
(check-sat)
