(declare-const s (Seq Int))
(declare-const t (Seq Int))
(declare-const j Int)
(declare-const b Int)

(assert (<= (seq.len s) 10))
(assert (= (seq.++ (seq.unit b) s) (seq.++ (seq.unit 42) t)))
(assert (= b 41))
(check-sat)