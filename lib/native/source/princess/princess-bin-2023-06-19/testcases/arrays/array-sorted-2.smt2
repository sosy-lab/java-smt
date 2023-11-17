

(declare-sort O 0)
(declare-const x (Array Int O))

(assert (= (select x 0) (select x 1)))

(check-sat)
