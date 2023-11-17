

(declare-const w String)
(declare-const v String)

(assert (distinct (str.indexof w w 0) 0))
(check-sat)
