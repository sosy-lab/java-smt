

(declare-const w String)

(assert (= (str.to_int w) 12345))
(check-sat)

