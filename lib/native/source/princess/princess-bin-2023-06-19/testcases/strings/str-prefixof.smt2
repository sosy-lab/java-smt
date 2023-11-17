

(declare-const w String)
(declare-const v String)

(assert (str.prefixof v w))
(assert (> (str.len v) 3))
(assert (= (str.len v) (str.len w)))

(check-sat)

