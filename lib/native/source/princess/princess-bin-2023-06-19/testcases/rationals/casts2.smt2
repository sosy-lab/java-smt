
(declare-const x Int)

; cannot be proven yet
(assert (not (= x (to_int (to_real x)))))

(check-sat)
(get-model)
