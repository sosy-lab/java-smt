; Example that is sat, but Princess previously reported unsat

(assert

 (forall ((x1 Real)) (forall ((x3 Real)) (exists ((x4 Real))
         
              (= (+ (+ (* (- 27) x1) (* 11 x3)) (* 17 x4)) (- 20)) ) 

             )))


(check-sat)
(exit)
