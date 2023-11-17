
(declare-const w String)
(declare-const n Int)

(assert (= (str.len w) 3))
(assert (= w (str.from_int n)))
(assert (< n 500))

(check-sat)
