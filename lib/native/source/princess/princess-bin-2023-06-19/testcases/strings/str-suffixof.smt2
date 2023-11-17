

(declare-const w String)
(declare-const v String)

(assert (str.suffixof v w))
(assert (str.prefixof "a" v))
(assert (> (str.len v) 3))
(assert (= (+ (str.len v) 2) (str.len w)))

(check-sat)

