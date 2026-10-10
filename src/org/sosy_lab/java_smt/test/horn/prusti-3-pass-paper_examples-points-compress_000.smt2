(set-logic HORN)

(declare-datatypes ((~Tup<%Point-%Point> 0) (%Point 0)) (((~tup<%Point-%Point>  (~at0/<%Point-%Point> %Point) (~at1/<%Point-%Point> %Point)))
                                                         ((%Point-0  (%Point-0.0 Int) (%Point-0.1 Int)))))
(declare-datatypes ((~Mut<%Point> 0)) (((~mut<%Point>  (~cur<%Point> %Point) (~ret<%Point> %Point)))))

(declare-fun |%main.2| ( ~Tup<%Point-%Point> Int Bool Bool ) Bool)
(declare-fun |%shift_x| ( ~Mut<%Point> Int ) Bool)
(declare-fun |%main| ( Bool ) Bool)

(assert
  (forall ( (A Int) (B ~Mut<%Point>) (C Bool) (D Int) (E ~Tup<%Point-%Point>) (F Bool) (G ~Tup<%Point-%Point>) (H %Point) (I %Point) ) 
    (=>
      (and
        (%main.2 E D C F)
        (%shift_x B A)
        (let ((a!1 (+ 1
              (%Point-0.0 (~at0/<%Point-%Point> G))
              (* (- 1) (%Point-0.0 (~at1/<%Point-%Point> G)))))
      (a!2 (= C (<= (%Point-0.0 H) (%Point-0.0 (~at0/<%Point-%Point> G))))))
  (and (= A a!1)
       (= D a!1)
       (= E (~tup<%Point-%Point> (~at0/<%Point-%Point> G) H))
       a!2
       (= H I)
       (= B (~mut<%Point> (~at1/<%Point-%Point> G) I))))
      )
      (%main F)
    )
  )
)
(assert
  (forall ( (A ~Tup<%Point-%Point>) (B Int) (C Bool) (v_3 Bool) ) 
    (=>
      (and
        (and (not C) (= v_3 false))
      )
      (%main.2 A B v_3 C)
    )
  )
)
(assert
  (forall ( (A ~Tup<%Point-%Point>) (B Int) (C Bool) (v_3 Bool) ) 
    (=>
      (and
        (and (= C true) (= v_3 true))
      )
      (%main.2 A B v_3 C)
    )
  )
)
(assert
  (forall ( (A ~Mut<%Point>) (B Int) ) 
    (=>
      (and
        (let ((a!1 (%Point-0 (+ (%Point-0.0 (~cur<%Point> A)) B)
                     (%Point-0.1 (~cur<%Point> A)))))
  (= (~ret<%Point> A) a!1))
      )
      (%shift_x A B)
    )
  )
)
(assert
  (forall ( (v_0 Bool) ) 
    (=>
      (and
        (%main v_0)
        (= v_0 true)
      )
      false
    )
  )
)

(check-sat)
(exit)
