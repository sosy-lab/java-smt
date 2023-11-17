(declare-const s (Seq Int))
(declare-const t (Seq Int))

(assert (= s (seq.++ (seq.unit 0) (seq.unit 1) (seq.unit 2))))
(assert (= t (seq.extract s 1 1)))
(assert (> (seq.nth t 0) 5))

(check-sat)
