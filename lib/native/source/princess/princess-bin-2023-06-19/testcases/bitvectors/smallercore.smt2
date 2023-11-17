(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source | From paper by Roberto Bruttomesso |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert
   (and
	(= ((_ extract 5 0) x) #b010110)
	(= ((_ extract 7 2) x) #b000110)
	(= x y)
   )
)	
(check-sat)


