
(declare-const leq (Array Int Int Bool))
(declare-const a Int)
(declare-const b Int)

(assert (= leq (lambda ((x Int) (y Int)) (<= x y))))
(assert (not (= (select leq a b) (<= a b))))

(check-sat)
