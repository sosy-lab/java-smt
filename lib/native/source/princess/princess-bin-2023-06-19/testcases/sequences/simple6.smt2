(declare-const s (Seq Int))
(declare-const t (Seq Int))

(assert (distinct s t))

(check-sat)
(get-model)
