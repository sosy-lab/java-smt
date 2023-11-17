

(declare-const w String)
(declare-const n Int)

(assert (= (str.substr w (- (str.len w) 3) 3) "abc"))
(assert (> (str.len w) 10))
(check-sat)

