

(declare-const w String)
(declare-const v String)

(assert (distinct v ""))
(assert (> (str.indexof w v 0) 0))
(check-sat)
