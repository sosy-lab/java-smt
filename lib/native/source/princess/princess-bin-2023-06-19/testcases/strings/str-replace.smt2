
(declare-const w String)
(declare-const v String)

(assert (= (str.replace w "a" "A") v))
(assert (str.contains w "bbaacc"))

(check-sat)

