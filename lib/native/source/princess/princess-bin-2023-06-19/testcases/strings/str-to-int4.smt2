

(declare-const w String)
(declare-const n Int)
(declare-const a Int)
(declare-const b Int)

(assert (= (* a b) n))
(assert (>= a 100))
(assert (>= b 100))
(assert (= (str.to_int w) n))
(assert (= (str.len w) 6))
(assert (= (str.at w 0) (str.at w 5)))
(assert (= (str.at w 1) (str.at w 4)))
(assert (= (str.at w 2) (str.at w 3)))
(assert (not (str.prefixof "0" w)))

(check-sat)
(get-model)

