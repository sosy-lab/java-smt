(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(declare-fun ab () (_ BitVec 8))
(declare-fun ba () (_ BitVec 8))

(assert
(and
  (= a #b0000)
  (= b #b1111)
  (= (concat a b) ab)
  (= (concat b a) ba)
  (= ab ba)
)
)
(check-sat)


