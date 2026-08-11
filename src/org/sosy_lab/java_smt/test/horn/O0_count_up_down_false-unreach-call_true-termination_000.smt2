(set-logic HORN)


(declare-fun |f1| ( Int ) Bool)
(declare-fun |f2| ( ) Bool)
(declare-fun |f3| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) )
    (=>
        true
      (f1 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) )
    (=>
      (and
        (f1 B)
        (and (or (= C H))
     (or (= F 0))
     (or (not D) (and E D)))
      )
      (f3 G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Int) (F Bool) (G Bool) (H Bool) (I Bool) (J Int) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) )
    (=>
      (and
        (f3 D E A)
        (let ((a!1 (or (not H) (not (= (= D E) F)))))
  (and (or C (not H) (not B))
       a!1
       (or (not H) (= J (ite F 1 0)))
       (or (and H B))
       (or (not G))
       (or (= K (= J 0)))
       (or (and L I))
       (or (and M L))
       (or (and N M))
       (or (and O N))
       (or K (not L))
       (= O true)
       (= C (= A 0))))
      )
      f2
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) )
    (=>
      (and
        f2
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
