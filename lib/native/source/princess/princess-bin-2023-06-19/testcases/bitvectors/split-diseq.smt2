(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 4))
(declare-fun d () (_ BitVec 4))
(assert
(and
  (not (= a b))
  (not (= c d))

  (= ((_ extract 7 4) a) c)
  (= ((_ extract 7 4) b) c)
  
  (= ((_ extract 3 0) a) d)
  (= ((_ extract 3 0) b) d)    
)
)
(check-sat)
