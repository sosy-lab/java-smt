

(declare-const w String)
(declare-const n Int)

(assert (str.in_re w (re.+ (re.union (str.to_re "a") (str.to_re "b")))))
(assert (= (str.len w) 2))
(assert (distinct w "aa" "ab" "ba" "bb"))

(check-sat)
