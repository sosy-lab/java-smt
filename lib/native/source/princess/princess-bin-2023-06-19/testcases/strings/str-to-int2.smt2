

(declare-const w String)

(assert (> (str.to_int w) 12345))
(assert (str.prefixof "31" w))
(check-sat)

