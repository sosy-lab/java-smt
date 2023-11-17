
(declare-const negate (Array Int Bool Int))
(declare-const a Int)
(declare-const b Int)

(assert (= negate (lambda ((x Int) (b Bool)) (ite b (- x) x))))
(assert (>= (select negate 42 true) 0))

(check-sat)
