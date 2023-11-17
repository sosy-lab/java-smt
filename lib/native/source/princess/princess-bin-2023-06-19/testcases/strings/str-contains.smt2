
(declare-const w String)

(assert (not (str.contains w "aa")))
(assert (str.contains w "a"))
(assert (str.contains w "b"))
(assert (str.contains w "c"))

(check-sat)

