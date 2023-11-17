(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun T1_572572 () (_ BitVec 8))
(assert (and true (= (bvand T1_572572 (_ bv16 8)) (_ bv0 8)) (= (bvand T1_572572 (_ bv1 8)) (_ bv0 8))))
(check-sat)
(exit)
