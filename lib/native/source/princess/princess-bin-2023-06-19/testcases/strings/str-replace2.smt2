
(declare-const w String)
(declare-const v String)

(assert (= (str.replace w "x" "X") v))
(assert (str.contains w "bbaacc"))
(assert (= (str.len w) 6))
(assert (str.contains v "X"))

(check-sat)

