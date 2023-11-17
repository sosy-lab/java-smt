; This example previously led to an exception, since the use
; of quantifiers make it necessary to call the ExhaustiveProver,
; for which model construction is more problematic

(set-logic AUFLIA)
(declare-fun PRED28 () Bool)
(declare-fun PRED27 () Bool)
(declare-fun PRED26 () Bool)
(declare-fun PRED25 () Bool)
(declare-fun PRED24 () Bool)
(declare-fun PRED23 () Bool)
(declare-fun PRED22 () Bool)
(declare-fun PRED21 () Bool)
(declare-fun PRED29 () Bool)
(declare-fun PRED31 () Bool)
(declare-fun PRED30 () Bool)
(declare-fun PRED17 () Bool)
(declare-fun PRED16 () Bool)
(declare-fun PRED15 () Bool)
(declare-fun PRED14 () Bool)
(declare-fun PRED13 () Bool)
(declare-fun PRED12 () Bool)
(declare-fun PRED11 () Bool)
(declare-fun PRED99 () Bool)
(declare-fun PRED10 () Bool)
(declare-fun PRED98 () Bool)
(declare-fun PRED19 () Bool)
(declare-fun PRED18 () Bool)
(declare-fun PRED20 () Bool)
(declare-fun PRED49 () Bool)
(declare-fun PRED48 () Bool)
(declare-fun PRED47 () Bool)
(declare-fun PRED46 () Bool)
(declare-fun PRED45 () Bool)
(declare-fun PRED44 () Bool)
(declare-fun PRED43 () Bool)
(declare-fun PRED53 () Bool)
(declare-fun PRED52 () Bool)
(declare-fun PRED51 () Bool)
(declare-fun PRED50 () Bool)
(declare-fun PRED39 () Bool)
(declare-fun PRED38 () Bool)
(declare-fun PRED37 () Bool)
(declare-fun PRED36 () Bool)
(declare-fun PRED35 () Bool)
(declare-fun PRED34 () Bool)
(declare-fun PRED33 () Bool)
(declare-fun PRED32 () Bool)
(declare-fun PRED42 () Bool)
(declare-fun PRED41 () Bool)
(declare-fun PRED40 () Bool)
(declare-fun PRED69 () Bool)
(declare-fun PRED68 () Bool)
(declare-fun PRED67 () Bool)
(declare-fun PRED66 () Bool)
(declare-fun PRED65 () Bool)
(declare-fun PRED75 () Bool)
(declare-fun PRED74 () Bool)
(declare-fun PRED73 () Bool)
(declare-fun PRED72 () Bool)
(declare-fun PRED71 () Bool)
(declare-fun PRED70 () Bool)
(declare-fun PRED0 () Bool)
(declare-fun PRED59 () Bool)
(declare-fun PRED58 () Bool)
(declare-fun PRED57 () Bool)
(declare-fun PRED56 () Bool)
(declare-fun PRED55 () Bool)
(declare-fun PRED54 () Bool)
(declare-fun PRED9 () Bool)
(declare-fun PRED6 () Bool)
(declare-fun PRED64 () Bool)
(declare-fun PRED5 () Bool)
(declare-fun PRED63 () Bool)
(declare-fun PRED8 () Bool)
(declare-fun PRED62 () Bool)
(declare-fun PRED7 () Bool)
(declare-fun PRED61 () Bool)
(declare-fun PRED2 () Bool)
(declare-fun PRED60 () Bool)
(declare-fun PRED1 () Bool)
(declare-fun PRED4 () Bool)
(declare-fun PRED3 () Bool)
(declare-fun PRED89 () Bool)
(declare-fun PRED88 () Bool)
(declare-fun PRED87 () Bool)
(declare-fun PRED97 () Bool)
(declare-fun PRED96 () Bool)
(declare-fun PRED95 () Bool)
(declare-fun PRED94 () Bool)
(declare-fun PRED93 () Bool)
(declare-fun PRED92 () Bool)
(declare-fun PRED91 () Bool)
(declare-fun PRED90 () Bool)
(declare-fun PRED79 () Bool)
(declare-fun PRED78 () Bool)
(declare-fun PRED77 () Bool)
(declare-fun PRED76 () Bool)
(declare-fun PRED109 () Bool)
(declare-fun PRED108 () Bool)
(declare-fun PRED86 () Bool)
(declare-fun PRED103 () Bool)
(declare-fun PRED85 () Bool)
(declare-fun PRED102 () Bool)
(declare-fun PRED84 () Bool)
(declare-fun PRED101 () Bool)
(declare-fun PRED83 () Bool)
(declare-fun PRED100 () Bool)
(declare-fun PRED82 () Bool)
(declare-fun PRED107 () Bool)
(declare-fun PRED81 () Bool)
(declare-fun PRED106 () Bool)
(declare-fun PRED80 () Bool)
(declare-fun PRED105 () Bool)
(declare-fun PRED104 () Bool)
(declare-fun |__ADDRESS_OF_main::x| () Int)
(declare-fun |sep::i| () Int)
(declare-fun |main::ret2@3| () Int)
(declare-fun |main::ret2@2| () Int)
(declare-fun |main::ret2@1| () Int)
(declare-fun |sep::x| () Int)
(declare-fun __+Infinity__ () Int)
(declare-fun |sep::ret@11| () Int)
(declare-fun |sep::ret@10| () Int)
(declare-fun |sep::ret@13| () Int)
(declare-fun __NaN__ () Int)
(declare-fun |sep::ret@12| () Int)
(declare-fun |main::i@5| () Int)
(declare-fun |main::i@4| () Int)
(declare-fun |main::i@6| () Int)
(declare-fun |sep::__retval__@2| () Int)
(declare-fun |main::ret@3| () Int)
(declare-fun |sep::__retval__@3| () Int)
(declare-fun |main::ret@2| () Int)
(declare-fun |sep::__retval__@4| () Int)
(declare-fun |main::ret@1| () Int)
(declare-fun |main::i@3| () Int)
(declare-fun |main::i@2| () Int)
(declare-fun |sep::i@5| () Int)
(declare-fun |sep::i@6| () Int)
(declare-fun |sep::i@7| () Int)
(declare-fun |sep::i@8| () Int)
(declare-fun |sep::ret| () Int)
(declare-fun |sep::i@9| () Int)
(declare-fun |main::ret| () Int)
(declare-fun |main::ret2| () Int)
(declare-fun |main::ret5| () Int)
(declare-fun |sep::i@20| () Int)
(declare-fun __-Infinity__ () Int)
(declare-fun |sep::i@15| () Int)
(declare-fun |sep::i@14| () Int)
(declare-fun |main::temp| () Int)
(declare-fun |main::ret5@2| () Int)
(declare-fun |sep::i@17| () Int)
(declare-fun |main::ret5@1| () Int)
(declare-fun |sep::i@16| () Int)
(declare-fun |sep::i@19| () Int)
(declare-fun |sep::i@2| () Int)
(declare-fun |sep::i@18| () Int)
(declare-fun |sep::i@3| () Int)
(declare-fun |sep::i@4| () Int)
(declare-fun __VERIFIER_error () Int)
(declare-fun |main::i| () Int)
(declare-fun |sep::i@11| () Int)
(declare-fun |sep::i@10| () Int)
(declare-fun |sep::i@13| () Int)
(declare-fun |sep::i@12| () Int)
(declare-fun |sep::ret@6| () Int)
(declare-fun |sep::ret@15| () Int)
(declare-fun |sep::ret@5| () Int)
(declare-fun |sep::ret@14| () Int)
(declare-fun |sep::ret@8| () Int)
(declare-fun |sep::ret@17| () Int)
(declare-fun |sep::ret@7| () Int)
(declare-fun |sep::ret@16| () Int)
(declare-fun |sep::x@2| () Int)
(declare-fun |sep::ret@19| () Int)
(declare-fun |sep::x@3| () Int)
(declare-fun |sep::ret@9| () Int)
(declare-fun |sep::ret@18| () Int)
(declare-fun |sep::x@4| () Int)
(declare-fun |sep::ret@2| () Int)
(declare-fun |main::ret5@3| () Int)
(declare-fun |sep::ret@4| () Int)
(declare-fun |sep::ret@3| () Int)
(declare-fun |main::temp@3| () Int)
(declare-fun |main::temp@4| () Int)
(declare-fun |sep::ret@20| () Int)
(declare-fun *signed_int@2 (Int) Int)
(push 1)
(push 1)
(assert (and (and (and (<= 0 (+ |__ADDRESS_OF_main::x| (- 1) ) ) (= |sep::x@2| |__ADDRESS_OF_main::x| ) ) (= |sep::ret@2| 0 ) ) (= |sep::i@2| 0 ) ) )
(push 1)
(assert (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= PRED2 (<= 0 (* (- 1) |sep::i@2| ) ) ) (= PRED4 (<= 0 (+ 1 (* (- 1) |sep::i@2| ) ) ) ) ) (= PRED5 (<= 0 (+ 2 (* (- 1) |sep::i@2| ) ) ) ) ) (= PRED6 (= |sep::i@2| 0 ) ) ) (= PRED7 (= |sep::i@2| 1 ) ) ) (= PRED8 (= |sep::i@2| 2 ) ) ) (= PRED9 (= |sep::i@2| 3 ) ) ) (= PRED10 (= |sep::i@2| 4 ) ) ) (= PRED16 (<= 0 (+ 3 (* (- 1) |sep::i@2| ) ) ) ) ) (= PRED17 (<= 0 (+ 4 (* (- 1) |sep::i@2| ) ) ) ) ) (= PRED18 (= (+ |sep::x@2| (+ (* 4 |sep::i@2| ) (* (- 1) |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) (= PRED19 (= |sep::ret@2| 0 ) ) ) (= PRED20 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 |__ADDRESS_OF_main::x| ) ) (- 1) ) ) ) ) (= PRED21 (= |sep::ret@2| (- 1) ) ) ) (= PRED22 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 |__ADDRESS_OF_main::x| ) ) 0 ) ) ) ) (= PRED23 (= |sep::ret@2| 1 ) ) ) (= PRED24 (= (+ |sep::x@2| (+ (* 4 |sep::i@2| ) (* (- 1) |__ADDRESS_OF_main::x| ) ) ) 4 ) ) ) (= PRED25 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 4 |__ADDRESS_OF_main::x| ) ) ) 1 ) ) ) ) (= PRED26 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 4 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) (= PRED27 (= |sep::ret@2| 2 ) ) ) (= PRED28 (= |sep::ret@2| (- 2) ) ) ) (= PRED29 (= (+ |sep::x@2| (+ (* 4 |sep::i@2| ) (* (- 1) |__ADDRESS_OF_main::x| ) ) ) 8 ) ) ) (= PRED30 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) (= PRED31 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) (= PRED32 (= |sep::ret@2| 3 ) ) ) (= PRED33 (= |sep::ret@2| (- 3) ) ) ) (= PRED34 (= (+ |sep::x@2| (+ (* 4 |sep::i@2| ) (* (- 1) |__ADDRESS_OF_main::x| ) ) ) 12 ) ) ) (= PRED35 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) (= PRED36 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) (= PRED37 (= |sep::ret@2| 4 ) ) ) (= PRED38 (= |sep::ret@2| (- 4) ) ) ) (= PRED39 (= (+ |sep::x@2| (+ (* 4 |sep::i@2| ) (* (- 1) |__ADDRESS_OF_main::x| ) ) ) 16 ) ) ) (= PRED40 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) (= PRED41 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) (= PRED42 (= |sep::ret@2| 5 ) ) ) (= PRED43 (= |sep::ret@2| (- 5) ) ) ) (= PRED49 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 |__ADDRESS_OF_main::x| ) ) 1 ) ) ) ) (= PRED51 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 4 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) (= PRED52 (= (+ |sep::ret@2| (* (- 1) |main::ret@2| ) ) (- 3) ) ) ) (= PRED53 (= (+ |sep::ret@2| (* (- 1) |main::ret@2| ) ) (- 5) ) ) ) (= PRED54 (= (+ |sep::ret@2| (* (- 1) |main::ret@2| ) ) (- 1) ) ) ) (= PRED55 (= (+ |sep::ret@2| (* (- 1) |main::ret@2| ) ) 1 ) ) ) (= PRED56 (= (+ |sep::ret@2| (* (- 1) |main::ret@2| ) ) 3 ) ) ) (= PRED57 (= (+ |sep::ret@2| (* (- 1) |main::ret@2| ) ) 5 ) ) ) (= PRED58 (= |sep::x@2| |__ADDRESS_OF_main::x| ) ) ) (= PRED59 (= (+ |sep::ret@2| (* (- 1) |main::ret@2| ) ) (- 2) ) ) ) (= PRED60 (= (+ |sep::ret@2| (* (- 1) |main::ret@2| ) ) (- 4) ) ) ) (= PRED61 (= |sep::ret@2| |main::ret@2| ) ) ) (= PRED62 (= (+ |sep::ret@2| (* (- 1) |main::ret@2| ) ) 2 ) ) ) (= PRED63 (= (+ |sep::ret@2| (* (- 1) |main::ret@2| ) ) 4 ) ) ) (= PRED64 
(exists ((var0 Int)) (= (* 2 var0 ) (- 1) ) ) ) ) (= PRED65 (= (+ |main::ret@2| (* (- 1) |sep::ret@2| ) ) 1 ) ) ) (= PRED66 (= (+ |main::ret@2| (* (- 1) |sep::ret@2| ) ) 3 ) ) ) (= PRED67 (= (+ |main::ret@2| (* (- 1) |sep::ret@2| ) ) (- 1) ) ) ) (= PRED68 (= (+ |main::ret@2| (* (- 1) |sep::ret@2| ) ) (- 3) ) ) ) (= PRED69 (= |main::ret@2| |sep::ret@2| ) ) ) (= PRED70 (= (+ |main::ret@2| (* (- 1) |sep::ret@2| ) ) 2 ) ) ) (= PRED71 (= (+ |main::ret@2| (* (- 1) |sep::ret@2| ) ) (- 2) ) ) ) (= PRED72 
(exists ((var0 Int)) (and (and (or (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) ) 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (+ (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) (* (- 1) var0 ) ) ) (- 1) ) ) ) (or (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 4 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 |__ADDRESS_OF_main::x| ) ) (- 1) ) ) (or (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and (= |main::ret@2| (- 5) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) (and (= |main::ret@2| (- 3) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (and (= |main::ret@2| (- 3) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) (and (= |main::ret@2| (- 1) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and (= |main::ret@2| (- 3) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) (and (= |main::ret@2| (- 1) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) (and (= |main::ret@2| (- 1) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) ) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 |__ADDRESS_OF_main::x| ) ) 0 ) ) (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and (= |main::ret@2| (- 3) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) (and (= |main::ret@2| (- 1) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) (and (= |main::ret@2| (- 1) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) (and (= |main::ret@2| (- 1) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (or (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (+ (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) (* (- 1) var0 ) ) ) (- 1) ) ) ) (and (= |main::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) (and (= |sep::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) ) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 4 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 |__ADDRESS_OF_main::x| ) ) (- 1) ) ) (or (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and (= |main::ret@2| (- 3) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) (and (= |main::ret@2| (- 1) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) (and (= |main::ret@2| (- 1) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) (and (= |main::ret@2| (- 1) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (and (= |main::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) ) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 |__ADDRESS_OF_main::x| ) ) 0 ) ) (or (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) (and (= |main::ret@2| (- 1) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (or (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (+ (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) (* (- 1) var0 ) ) ) (- 1) ) ) ) (and (= |main::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) (and (= |sep::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) (and (= |main::ret@2| (- 1) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (or (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (+ (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) (* (- 1) var0 ) ) ) (- 1) ) ) ) (and (= |main::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) (and (= |sep::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (or (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (+ (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) (* (- 1) var0 ) ) ) (- 1) ) ) ) (and (= |main::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) (and (= |sep::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (or (or 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (+ (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) (* (- 1) var0 ) ) ) (- 1) ) ) (and (= |main::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) (and (= |sep::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (and (= |main::ret@2| 5 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) (and (= |main::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) ) ) ) ) ) ) ) ) ) (or (not (= |sep::i@2| 5 ) ) (= (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) var0 ) ) ) ) ) ) (= PRED73 
(exists ((var0 Int)) (and (and (= |main::ret@2| |sep::ret@2| ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 4 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 |__ADDRESS_OF_main::x| ) ) 0 ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (or (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (+ (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) (* (- 1) var0 ) ) ) (- 1) ) ) ) (and (= |main::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) (and (= |sep::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (or (or 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (+ (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) (* (- 1) var0 ) ) ) (- 1) ) ) (and (= |main::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) (and (= |sep::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (and (= |main::ret@2| 5 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) (and (= |main::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) ) ) ) ) ) ) (or (not (= |sep::i@2| 5 ) ) (= (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) var0 ) ) ) ) ) ) (= PRED74 
(exists ((var0 Int)) (and (and (= |main::ret@2| |sep::ret@2| ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 4 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 |__ADDRESS_OF_main::x| ) ) 0 ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) (or (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) (and (= |main::ret@2| (- 1) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) ) (and 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) (or (or (or (or 
(exists ((var1 Int)) (= (* 2 var1 ) (- 1) ) ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (+ (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) (* (- 1) var0 ) ) ) (- 1) ) ) ) (and (= |main::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) (and (= |main::ret@2| 1 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) ) ) ) (and (= |sep::ret@2| 3 ) 
(exists ((var1 Int)) (= (+ (* 2 var1 ) (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) ) ) ) ) ) (or (not (= |sep::i@2| 5 ) ) (= (*signed_int@2 (+ 16 |__ADDRESS_OF_main::x| ) ) var0 ) ) ) ) ) ) (= PRED75 
(exists ((var0 Int)) (and (and (= |main::ret@2| |sep::ret@2| ) (and (= (+ (* 2 var0 ) (*signed_int@2 (+ 4 |__ADDRESS_OF_main::x| ) ) ) 0 ) (and (= (+ (* 2 var0 ) (*signed_int@2 |__ADDRESS_OF_main::x| ) ) 0 ) (and (= (+ (* 2 var0 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) (= (+ (* 2 var0 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) (= (* (- 2) var0 ) 1 ) ) ) ) ) (= PRED76 (= |sep::i@2| 5 ) ) ) (= PRED77 
(exists ((var0 Int)) (and (= (+ (* 2 var0 ) (*signed_int@2 (+ 4 |__ADDRESS_OF_main::x| ) ) ) 0 ) (and (= (+ (* 2 var0 ) (*signed_int@2 |__ADDRESS_OF_main::x| ) ) 0 ) (and (= (+ (* 2 var0 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) (= (+ (* 2 var0 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) ) ) (= PRED78 
(exists ((var0 Int)) (and (and (= |main::ret@2| |sep::ret@2| ) (and (= (+ (* 2 var0 ) (*signed_int@2 (+ 4 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) (and (= (+ (* 2 var0 ) (*signed_int@2 |__ADDRESS_OF_main::x| ) ) 0 ) (and (= (+ (* 2 var0 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) 0 ) (= (+ (* 2 var0 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) (= (* (- 2) var0 ) 1 ) ) ) ) ) (= PRED79 
(exists ((var0 Int)) (and (= (+ (* 2 var0 ) (*signed_int@2 (+ 4 |__ADDRESS_OF_main::x| ) ) ) (- 1) ) (and (= (+ (* 2 var0 ) (*signed_int@2 |__ADDRESS_OF_main::x| ) ) 0 ) (and (= (+ (* 2 var0 ) (*signed_int@2 (+ 8 |__ADDRESS_OF_main::x| ) ) ) 0 ) (= (+ (* 2 var0 ) (*signed_int@2 (+ 12 |__ADDRESS_OF_main::x| ) ) ) 0 ) ) ) ) ) ) ) (= PRED80 (<= 0 (+ 5 (* (- 1) |sep::i@2| ) ) ) ) ) (= PRED89 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 12 (+ |sep::x@2| (* 4 |sep::i@2| ) ) ) ) ) (- 1) ) ) ) ) (= PRED90 (= (+ |sep::ret@2| (* (- 1) |main::ret2@2| ) ) (- 3) ) ) ) (= PRED91 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 12 (+ |sep::x@2| (* 4 |sep::i@2| ) ) ) ) ) 0 ) ) ) ) (= PRED92 (= (+ |sep::ret@2| (* (- 1) |main::ret2@2| ) ) (- 5) ) ) ) (= PRED93 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 8 (+ |sep::x@2| (* 4 |sep::i@2| ) ) ) ) ) 0 ) ) ) ) (= PRED94 (= (+ |sep::ret@2| (* (- 1) |main::ret2@2| ) ) (- 1) ) ) ) (= PRED95 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 8 (+ |sep::x@2| (* 4 |sep::i@2| ) ) ) ) ) (- 1) ) ) ) ) (= PRED96 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 4 (+ |sep::x@2| (* 4 |sep::i@2| ) ) ) ) ) 0 ) ) ) ) (= PRED97 (= (+ |sep::ret@2| (* (- 1) |main::ret2@2| ) ) 1 ) ) ) (= PRED98 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 4 (+ |sep::x@2| (* 4 |sep::i@2| ) ) ) ) ) (- 1) ) ) ) ) (= PRED99 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 16 (+ |sep::x@2| (* 4 |sep::i@2| ) ) ) ) ) 0 ) ) ) ) (= PRED100 (= (+ |sep::ret@2| (* (- 1) |main::ret2@2| ) ) 3 ) ) ) (= PRED101 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ 16 (+ |sep::x@2| (* 4 |sep::i@2| ) ) ) ) ) (- 1) ) ) ) ) (= PRED102 
(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ |sep::x@2| (* 4 |sep::i@2| ) ) ) ) 0 ) ) ) ) (= PRED103 (= (+ |sep::ret@2| (* (- 1) |main::ret2@2| ) ) 5 ) ) ) (= PRED104 

(exists ((var0 Int)) (= (+ (* 2 var0 ) (*signed_int@2 (+ |sep::x@2| (* 4 |sep::i@2| ) ) ) ) (- 1) ) )

 ) ) (= PRED105 (= (+ |sep::ret@2| (* (- 1) |main::ret2@2| ) ) (- 2) ) ) ) (= PRED106 (= (+ |sep::ret@2| (* (- 1) |main::ret2@2| ) ) (- 4) ) ) ) (= PRED107 (= |sep::ret@2| |main::ret2@2| ) ) ) (= PRED108 (= (+ |sep::ret@2| (* (- 1) |main::ret2@2| ) ) 2 ) ) ) (= PRED109 (= (+ |sep::ret@2| (* (- 1) |main::ret2@2| ) ) 4 ) ) ) )
(push 1)
(check-sat)
(get-value ( PRED2 ))
(get-value ((not PRED2 )))
(pop 1)
(pop 1)
(pop 1)

