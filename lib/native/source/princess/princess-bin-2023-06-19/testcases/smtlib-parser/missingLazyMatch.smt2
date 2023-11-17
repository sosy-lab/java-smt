(set-logic AUFNIRA)
(set-info :source |
    SMT script generated on 2015/02/11 by Ultimate. http://ultimate.informatik.uni-freiburg.de/
|)
(set-info :smt-lib-version 2.0)

(declare-fun |c_main_~#a~4.base| () Int)
(declare-fun |c_old(#valid)| () (Array Int Bool))
(declare-fun |c_#valid| () (Array Int Bool))

(assert (and 

(and (forall ((var0 Int)) (or (or (or (= var0 |c_main_~#a~4.base|) (= var0 0)) (not (select |c_old(#valid)| var0))) (select |c_#valid| var0))) (and (and (or (or (forall ((var0 Int)) (or (= var0 |c_main_~#a~4.base|) (= var0 0))) (not (select |c_old(#valid)| |c_main_~#a~4.base|))) (= |c_main_~#a~4.base| 0)) (and (forall ((var0 Int)) (forall ((var1 Int)) (or (or (or (= var0 |c_main_~#a~4.base|) (= var0 0)) (not (select |c_old(#valid)| var1))) (or (= var1 0) (select |c_#valid| var1))))) (forall ((var0 Int)) (or (or (or (= var0 |c_main_~#a~4.base|) (= var0 0)) (not (select |c_old(#valid)| var0))) (or (= var0 0) (or (select |c_#valid| var0) (not (select |c_old(#valid)| var0)))))))) (and (or (or (forall ((var0 Int)) (or (= var0 |c_main_~#a~4.base|) (= var0 0))) (not (select |c_old(#valid)| |c_main_~#a~4.base|))) (not (select |c_old(#valid)| 0))) (and (forall ((var0 Int)) (forall ((var1 Int)) (or (or (or (= var0 |c_main_~#a~4.base|) (= var0 0)) (not (select |c_old(#valid)| var1))) (or (not (select |c_old(#valid)| 0)) (select |c_#valid| var1))))) (forall ((var0 Int)) (or (or (or (= var0 |c_main_~#a~4.base|) (= var0 0)) (not (select |c_old(#valid)| var0))) (or (not (select |c_old(#valid)| 0)) (or (select |c_#valid| var0) (not (select |c_old(#valid)| var0)))))))))) 

(forall ((var0 Int)) (or (or (= var0 |c_main_~#a~4.base|) (select |c_old(#valid)| var0)) (not (select |c_#valid| var0))))))

(check-sat)
