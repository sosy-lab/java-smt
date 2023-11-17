(reset)
(set-logic AUFLIA)
; (add-theories GroebnerMultiplication)
(declare-fun p1 () Bool)
(declare-fun FALSE_local0 () Int)
(declare-fun FALSE_local1 () Int)
(declare-fun FALSE_local2 () Int)
(declare-fun FALSE_local3 () Int)
(declare-fun FALSE_local4 () Int)
(declare-fun FALSE_local5 () Int)
(declare-fun FALSE_local6 () Int)
; (push 1)
(assert (and 

(>= (-  540 FALSE_local0 )  0 )
 
p1 
 
(= (*  24945510 FALSE_local6  FALSE_local6 ) FALSE_local3)
(= (* 292681 FALSE_local6  FALSE_local6)  FALSE_local5)  
(= (* FALSE_local5  FALSE_local6 ) FALSE_local4)  
(= (* (* 2266521664 FALSE_local4)  (- (* 292681 FALSE_local1) 318) ) FALSE_local0)  
(= (* 158340421 FALSE_local3  FALSE_local6 ) FALSE_local2)  
(= (* FALSE_local2  FALSE_local6 ) FALSE_local1)

))

; adding internal formula: NegLazyConjunction(AtomicLazyConjunction((-1*FALSE_local0 + 540 >= 0 & p1 & mul(24945510*FALSE_local6, FALSE_local6, FALSE_local3) & mul(292681*FALSE_local6, FALSE_local6, FALSE_local5) & mul(FALSE_local5, FALSE_local6, FALSE_local4) & mul(2266521664*FALSE_local4, 292681*FALSE_local1 + -318, FALSE_local0) & mul(158340421*FALSE_local3, FALSE_local6, FALSE_local2) & mul(FALSE_local2, FALSE_local6, FALSE_local1)),List(FALSE_local6, FALSE_local5, FALSE_local4, FALSE_local3, FALSE_local2, FALSE_local1, FALSE_local0), List(p1/0, mul/3)))

(check-sat)
(exit)
