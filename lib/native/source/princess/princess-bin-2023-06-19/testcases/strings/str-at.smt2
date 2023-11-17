

(declare-const w String)
(declare-const n Int)

(assert (= (str.at w n) "a"))
(check-sat)

