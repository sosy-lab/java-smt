(set-info :smt-lib-version 2.6)
(declare-fun x () (_ BitVec 2))
(declare-fun z () (_ BitVec 8))

(assert
   (and
	; (= z #b00001111)
	(= ((_ extract 7 4) z) #b0000)
	(= ((_ extract 3 0) z) #b1111)	
	; (not (= ((_ extract 7 4) z) ((_ extract 3 0) z)))
	(= x ((_ extract 1 0) z))
	(or
	  (= x ((_ extract 7 6) z))
	  (= x ((_ extract 6 5) z))	  
	  ; (= x ((_ extract 1 0) z))	  
	)
   )	
)	
(check-sat)