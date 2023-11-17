

(declare-const w String)
(declare-const v String)

(assert (<= (str.len v) 10))
(assert (<= (str.len w) 10))

(assert (not
   (=>
      (> (str.len v) (str.len w))
      (= (str.indexof w v 0) (- 1)))))

(check-sat)
