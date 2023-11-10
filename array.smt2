(declare-const x Int)
(declare-const y Int)
(declare-const a1 (Array Int Int))
(declare-const a2 (Array Int Int))
(assert (= (select a1 x) x))
(assert (= (store a1 x y) a1))
(check-sat)
(get-model)

