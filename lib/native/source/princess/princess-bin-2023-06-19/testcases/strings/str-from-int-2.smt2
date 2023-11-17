
(declare-const w String)
(declare-const n Int)

(assert (<= (str.len w) 2))
(assert (= w (str.from_int n)))
(assert (> n 500))

(check-sat)
