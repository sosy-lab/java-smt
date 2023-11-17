
(declare-fun f (String) Int)

(declare-const x String)
(declare-const y String)

(assert (= (f x) 1))
(assert (= (f y) 2))

(assert (= x "aaaaa"))

(check-sat)
(get-model)
