(declare-fun x1 () (_ BitVec 8))
(declare-fun x2 () (_ BitVec 8))
(declare-fun y () (_ BitVec 2))
(declare-fun z () (_ BitVec 6))
(assert
  (and
   (= (concat y z) x2)
   (= x1 x2)
   (= ((_ extract 0 0) x1) #b0)
   (= ((_ extract 0 0) z) #b1)
  )
)
(check-sat)


