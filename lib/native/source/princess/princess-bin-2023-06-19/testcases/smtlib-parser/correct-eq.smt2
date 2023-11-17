(set-logic AUFLIA)
(declare-fun p1 () Bool)
(declare-fun p2 () Bool)
(declare-fun p3 () Bool)

(assert (not (= (= p1 p2 p3)
                (and (= p1 p2) (= p2 p3)))))
(check-sat)
(exit)