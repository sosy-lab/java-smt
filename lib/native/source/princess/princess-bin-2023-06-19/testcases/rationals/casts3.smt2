
(declare-const x Real)

(assert (not (is_int x)))

(check-sat)
(get-model)
