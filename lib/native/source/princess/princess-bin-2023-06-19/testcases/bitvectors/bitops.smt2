(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.

|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun x () (_ BitVec 2))
(declare-fun z () (_ BitVec 2))
(assert
(not
  (and
    (and
      (and
        (and
	  (and
	    (and
	      (and
	        (and
		  (and
  		    ; (= ((_ extract 6 6) (bvnot (concat (concat x (_ bv5 3)) z))) (_ bv0 1))
		      (= ((_ extract 3 3) (bvnot (concat (_ bv3 3) z))) (_ bv0 1))
		  )
		)
	      )
	    )
	  )
	)
      )
    )
  )
)
)
(check-sat)
(exit)
