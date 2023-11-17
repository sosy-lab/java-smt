(set-logic AUFLIA)
(set-option :produce-interpolants true)

(declare-datatypes () ((Col red blue)))

(declare-const x Col)

(assert (not (= x red)))
(assert (not (= x blue)))

(check-sat)
(get-interpolants)
