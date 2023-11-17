

(declare-const w String)

(assert (< (str.to_int w) 10))
(assert (>= (str.to_int w) 0))
(assert (str.prefixof "31" w))
(check-sat)

