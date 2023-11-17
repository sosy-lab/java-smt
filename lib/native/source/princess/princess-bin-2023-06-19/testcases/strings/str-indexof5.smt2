(set-logic QF_SLIA)

(declare-const X String)

(assert (and
  (= X "")
  (not (str.contains X ":"))
))
(check-sat)
(get-model)

