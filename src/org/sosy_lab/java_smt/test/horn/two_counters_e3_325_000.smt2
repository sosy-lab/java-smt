(set-logic HORN)


(declare-fun |state| ( Int Bool Bool Int Bool Bool Bool Bool Bool Bool Bool Bool Int ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Int) (E Int) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Int) ) 
    (=>
      (and
        (and (= E D)
     (= (= D 2) J)
     (= (= H G) F)
     (= (and A K) I)
     (= J H)
     (= I G)
     (= B K)
     (= C A)
     (not B)
     (not C)
     (= E 0))
      )
      (state E C B D J A K I H G F L M)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Int) (E Int) (F Bool) (G Bool) (H Int) (I Int) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Int) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Int) (Z Bool) ) 
    (=>
      (and
        (state E C B D V A W U T S R X Y)
        (let ((a!1 (or (= D 3) (= (+ D (* (- 1) H)) 1))))
  (and (= Q I)
       (= E D)
       (= (= Q 2) N)
       (= (= D 2) V)
       (= (= T S) R)
       (= (= L K) J)
       (= (and P O) M)
       (= (and A W) U)
       (= W G)
       (= V T)
       (= U S)
       (= M K)
       (= N L)
       (= O F)
       (= P G)
       (= C A)
       (= B W)
       (not (= A F))
       a!1
       (or (not (= D 3)) (= H 0))
       (= I H)))
      )
      (state I G F Q N P O M L K J Z H)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Int) (E Int) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Int) ) 
    (=>
      (and
        (state E C B D J A K I H G F L M)
        (not F)
      )
      false
    )
  )
)

(check-sat)
(exit)
