(assert (= (to_int (- 1.0)) (- (to_int 3.4) (to_int 2147483.647))))
(check-sat)
(exit)