(declare-const s (Seq Int))
(declare-const t (Seq Int))
(declare-const j Int)
(declare-const b Int)

(assert (= (seq.++ s (seq.unit b)) (seq.++ t (seq.unit 42))))
(assert (= b 41))
(check-sat)