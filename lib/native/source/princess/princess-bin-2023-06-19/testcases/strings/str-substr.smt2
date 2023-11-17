

(declare-const w String)
(declare-const n Int)

(assert (= (str.substr w n 3) "abc"))
(check-sat)

