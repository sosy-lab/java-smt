(reset)
(set-logic AUFLIA)
(declare-fun R0 () Int)
(declare-fun R1 () Int)
(declare-fun R2 () Int)
(declare-fun R3 () Int)
(declare-fun c4 () Int)
(declare-fun c5 () Int)
(declare-fun c6 () Int)
(declare-fun c7 () Int)
(declare-fun c8 () Int)
(declare-fun c9 () Int)
(declare-fun c10 () Int)
(declare-fun c11 () Int)
(declare-fun c12 () Int)
(declare-fun c13 () Int)
(declare-fun c14 () Int)
(declare-fun c15 () Int)
(declare-fun c16 () Int)
(declare-fun c17 () Int)
(declare-fun c18 () Int)
(declare-fun c19 () Int)
(declare-fun c20 () Int)
(assert (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (or (or (not (= (+ c20 (+ (* (- 1) c18) c17)) 0)) (not (= (+ c19 (+ (* (- 1) c18) c17)) (- 1)))) (or (<= 0 (+ 2 (+ (* (- 1) c18) c17))) (<= 0 (* (- 1) c17)))) (or (or (not (= (+ c20 (+ (* (- 1) c18) c17)) 0)) (not (= (+ c19 (+ (* (- 1) c18) c17)) 0))) (or (<= 0 (+ 1 (+ (* (- 1) c18) c17))) (<= 0 (* (- 1) c17))))) (or (or (not (= (+ c20 (+ (* (- 1) c18) c17)) 0)) (not (= c19 0))) (or (<= 0 (+ 1 (+ (* (- 1) c18) c17))) (<= 0 (* (- 1) c17))))) (or (or (or (not (= c20 c18)) (not (= (+ c19 (* (- 1) c18)) (- 1)))) (not (= c17 0))) (<= 0 (+ 2 (* (- 1) c18))))) (or (or (or (not (= c20 c18)) (not (= c19 c18))) (not (= c17 0))) (<= 0 (+ 1 (* (- 1) c18))))) (or (or (or (not (= c20 c18)) (not (= c19 1))) (not (= c17 0))) (<= 0 (+ 2 (* (- 1) c18))))) (or (or (or (not (= c20 c18)) (not (= c19 0))) (not (= c17 0))) (<= 0 (+ 1 (* (- 1) c18))))) (or (or (or (not (= c20 2)) (not (= c19 1))) (not (= (+ c18 (* (- 1) c17)) 2))) (<= 0 (* (- 1) c17)))) (or (or (or (not (= c20 2)) (not (= c19 1))) (not (= c18 2))) (not (= c17 0)))) (or (or (or (not (= c20 1)) (not (= c19 1))) (not (= (+ c18 (* (- 1) c17)) 1))) (<= 0 (* (- 1) c17)))) (or (or (or (not (= c20 1)) (not (= c19 1))) (not (= c18 1))) (not (= c17 0)))) (or (or (or (not (= c20 1)) (not (= c19 0))) (not (= (+ c18 (* (- 1) c17)) 1))) (<= 0 (* (- 1) c17)))) (or (or (or (not (= c20 1)) (not (= c19 0))) (not (= c18 1))) (not (= c17 0)))) (or (or (or (not (= c20 1)) (not (= c19 0))) (not (= c17 0))) (<= 0 (+ 1 (* (- 1) c18))))) (or (or (not (= c20 1)) (not (= c19 0))) (or (<= 0 (+ 1 (+ (* (- 1) c18) c17))) (<= 0 (* (- 1) c17))))) (or (or (not (= c19 1)) (not (= c17 0))) (or (<= 0 (+ c20 (* (- 1) c18))) (<= 0 (+ 2 (* (- 1) c20)))))) (or (or (not (= c19 0)) (not (= c17 0))) (or (<= 0 (+ c20 (* (- 1) c18))) (<= 0 (+ 1 (* (- 1) c20)))))) (or (not (= c19 0)) (or (or (<= 0 (+ c20 (+ (* (- 1) c18) c17))) (<= 0 (+ 1 (* (- 1) c20)))) (<= 0 (* (- 1) c17))))))
(assert (and (and (and (and (and (and (and (and (and (and (and (and (<= 0 c13) (<= 0 c4)) (<= 0 c16)) (<= 0 c14)) (<= 0 c9)) (<= 0 c12)) (<= 0 c11)) (<= 0 c6)) (<= 0 c5)) (<= 0 c15)) (<= 0 c7)) (<= 0 c10)) (<= 0 c8)))
(assert (and (and (and (= c6 c17) (= (+ (+ (+ (+ (+ (+ (+ (+ (+ (* 1 c4) (* 1 c5)) (* 1 c6)) (* 1 c7)) (* 1 c8)) (* 1 c9)) (* 1 c11)) (* 1 c12)) (* 1 c13)) (* 1 c15)) c18)) (= (+ (* 1 c5) (* 1 c13)) c19)) (= (+ (+ (+ (+ (+ (+ (+ (* 1 c4) (* 1 c5)) (* 1 c7)) (* 1 c8)) (* 1 c11)) (* 1 c12)) (* 1 c13)) (* 1 c15)) c20)))
(assert (= (* (- 1) c10) c14))
(assert (= (+ (+ (+ (* (- 1) c5) c12) c14) c15) 0))
(assert (= (+ (+ (+ (+ (* (- 1) c4) (* (- 1) c7)) c10) (* (- 1) c12)) (* (- 1) c15)) (- 1)))
(assert (= (+ (+ c4 c5) c7) 1))

(check-sat)

(assert (or (not (<= 0 (+ c13 (- 1)))) (<= 0 (+ c5 (- 1)))))

(check-sat)
(get-value ((or (not (<= 0 (+ c13 (- 1)))) (<= 0 (+ c5 (- 1))))))




;(get-value ((or (not (<= 0 (+ c13 (- 1)))) (<= 0 (+ c5 (- 1))))))

(assert (or (or (or (not (= c20 2)) (not (= c19 1))) (not (= c17 0))) (<= 0 (+ 2 (* (- 1) c18)))))
(check-sat)

(get-value ((or (not (<= 0 (+ c13 (- 1)))) (<= 0 (+ c5 (- 1))))))



(exit)


;(get-value ((or (or (or (not (= c20 2)) (not (= c19 1))) (not (= c17 0))) (<= 0 (+ 2 (* (- 1) c18))))))

(assert     (or (not (<= 0 (+ c13 (- 1)))) (<= 0 (+ c5 (- 1)))))
(check-sat)
(get-value ((or (not (<= 0 (+ c13 (- 1)))) (<= 0 (+ c5 (- 1))))))
(get-model)

