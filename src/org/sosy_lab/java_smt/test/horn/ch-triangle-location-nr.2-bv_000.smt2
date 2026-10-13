(set-logic HORN)


(declare-fun |combined_lturn__bar| ( (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(declare-fun |step_lturn| ( (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(declare-fun |lturn| ( (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(declare-fun |step_lturn__bar| ( (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |combined_lturn| ( (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (and (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff F) B))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff F) I))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff F) A))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff L) B))
     (bvsle #x00000000 (bvadd #xfffffffe G (bvmul #xffffffff L)))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff J) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff F) J))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff F) L))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff A) B))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff L) A))
     (bvsle #x00000000 (bvadd #xffffffff G (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xffffffff G (bvmul #xffffffff A)))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff D) E))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff C) H))
     (bvsle #x00000000 (bvadd G (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd G (bvmul #xffffffff B)))
     (bvsle #x00000000 (bvadd C (bvmul #xffffffff H)))
     (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff F) G)))
      )
      (lturn L A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (and (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff F) B))
     (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff L) B))
     (bvsle #x00000000 (bvadd #xfffffffd G (bvmul #xffffffff L)))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff F) I))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff A) B))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff L) I))
     (bvsle #x00000000 (bvadd #xfffffffe G (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xfffffffe G (bvmul #xffffffff A)))
     (bvsle #x00000000 (bvadd #xfffffffe B (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff J) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff F) J))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff F) A))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff A) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff L) J))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff L) A))
     (bvsle #x00000000 (bvadd #xffffffff G (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd #xffffffff B (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff F) L))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff D) E))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff C) H))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff A) J))
     (bvsle #x00000000 (bvadd G (bvmul #xffffffff B)))
     (bvsle #x00000000 (bvadd C (bvmul #xffffffff H)))
     (bvsle #x00000000 (bvadd A (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff F) G)))
      )
      (lturn L A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (and (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff F) B))
     (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff L) B))
     (bvsle #x00000000 (bvadd #xfffffffd G (bvmul #xffffffff L)))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff F) I))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff F) A))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff L) I))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff L) A))
     (bvsle #x00000000 (bvadd #xfffffffe G (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xfffffffe B (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff J) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff F) J))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff A) B))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff L) J))
     (bvsle #x00000000 (bvadd #xffffffff G (bvmul #xffffffff A)))
     (bvsle #x00000000 (bvadd #xffffffff A (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff F) L))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff D) E))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff C) H))
     (bvsle #x00000000 (bvadd G (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd G (bvmul #xffffffff B)))
     (bvsle #x00000000 (bvadd C (bvmul #xffffffff H)))
     (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff F) G)))
      )
      (lturn L A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (and (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff F) B))
     (bvsle #x00000000 (bvadd #xfffffffd G (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xfffffffd B (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff F) A))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff L) B))
     (bvsle #x00000000 (bvadd #xfffffffe G (bvmul #xffffffff L)))
     (bvsle #x00000000 (bvadd #xfffffffe A (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff J) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff F) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff F) L))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff A) B))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff L) A))
     (bvsle #x00000000 (bvadd #xffffffff G (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd #xffffffff G (bvmul #xffffffff A)))
     (bvsle #x00000000 (bvadd #xffffffff L (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff F) J))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff D) E))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff C) H))
     (bvsle #x00000000 (bvadd G (bvmul #xffffffff B)))
     (bvsle #x00000000 (bvadd C (bvmul #xffffffff H)))
     (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff F) G)))
      )
      (lturn L A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (and (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff F) B))
     (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff L) B))
     (bvsle #x00000000 (bvadd #xfffffffd G (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xfffffffd G (bvmul #xffffffff L)))
     (bvsle #x00000000 (bvadd #xfffffffd B (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff F) A))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff L) A))
     (bvsle #x00000000 (bvadd #xfffffffe G (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd #xfffffffe B (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd #xfffffffe A (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff J) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff F) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff A) B))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff L) I))
     (bvsle #x00000000 (bvadd #xffffffff G (bvmul #xffffffff A)))
     (bvsle #x00000000 (bvadd #xffffffff A (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff F) J))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff F) L))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff D) E))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff C) H))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff L) J))
     (bvsle #x00000000 (bvadd G (bvmul #xffffffff B)))
     (bvsle #x00000000 (bvadd C (bvmul #xffffffff H)))
     (bvsle #x00000000 (bvadd L (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff F) G)))
      )
      (lturn L A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (and (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff F) B))
     (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff L) B))
     (bvsle #x00000000 (bvadd #xfffffffd G (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xfffffffd G (bvmul #xffffffff L)))
     (bvsle #x00000000 (bvadd #xfffffffd B (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff A) B))
     (bvsle #x00000000 (bvadd #xfffffffe G (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd #xfffffffe G (bvmul #xffffffff A)))
     (bvsle #x00000000 (bvadd #xfffffffe B (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff J) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff F) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff F) A))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff L) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff L) A))
     (bvsle #x00000000 (bvadd #xffffffff A (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff F) J))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff F) L))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff D) E))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff C) H))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff A) I))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff L) J))
     (bvsle #x00000000 (bvadd G (bvmul #xffffffff B)))
     (bvsle #x00000000 (bvadd C (bvmul #xffffffff H)))
     (bvsle #x00000000 (bvadd A (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd L (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xfffffffd (bvmul #xffffffff F) G)))
      )
      (lturn L A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (and (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff F) B))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff L) B))
     (bvsle #x00000000 (bvadd #xfffffffe G (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xfffffffe G (bvmul #xffffffff L)))
     (bvsle #x00000000 (bvadd #xfffffffe B (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff J) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff F) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff F) A))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff A) B))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff L) I))
     (bvsle #x00000000 (bvadd #xffffffff (bvmul #xffffffff L) A))
     (bvsle #x00000000 (bvadd #xffffffff G (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd #xffffffff G (bvmul #xffffffff A)))
     (bvsle #x00000000 (bvadd #xffffffff B (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd #xffffffff A (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff F) J))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff F) L))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff D) E))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff C) H))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff A) I))
     (bvsle #x00000000 (bvadd (bvmul #xffffffff L) J))
     (bvsle #x00000000 (bvadd G (bvmul #xffffffff B)))
     (bvsle #x00000000 (bvadd C (bvmul #xffffffff H)))
     (bvsle #x00000000 (bvadd A (bvmul #xffffffff I)))
     (bvsle #x00000000 (bvadd L (bvmul #xffffffff J)))
     (bvsle #x00000000 (bvadd #xfffffffe (bvmul #xffffffff F) G)))
      )
      (step_lturn__bar L A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (lturn L A B C D E F G H I J K)
        true
      )
      (combined_lturn L A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (step_lturn L A B C D E F G H I J K)
        true
      )
      (combined_lturn L A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (step_lturn__bar L A B C D E F G H I J K)
        true
      )
      (combined_lturn__bar L A B C D E F G H I J K)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (step_lturn I A B C D E F G K J L H)
        true
      )
      (lturn I A B C D E F G L K J H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (step_lturn__bar I A B C D E F G L J K H)
        true
      )
      (lturn I A B C D E F G L K J H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (v_12 (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn I A B C D E F G v_12 J L H)
        (step_lturn I A B C D E F G v_13 K J H)
        (combined_lturn I A B C D E F G v_14 L K H)
        (and (= v_12 I) (= v_13 I) (= v_14 I))
      )
      (lturn I A B C D E F G L K J H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (v_12 (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn I A B C D E F G v_12 J L H)
        (combined_lturn I A B C D E F G v_13 K J H)
        (step_lturn I A B C D E F G v_14 L K H)
        (and (= v_12 I) (= v_13 I) (= v_14 I))
      )
      (lturn I A B C D E F G L K J H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (v_12 (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) )
    (=>
      (and
        (step_lturn I A B C D E F G v_12 J L H)
        (combined_lturn I A B C D E F G v_13 K J H)
        (combined_lturn I A B C D E F G v_14 L K H)
        (and (= v_12 I) (= v_13 I) (= v_14 I))
      )
      (lturn I A B C D E F G L K J H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn J A B C D E F G I L v_13 H)
        (step_lturn J A B C D E F G M L K H)
        (combined_lturn J A B C D E F G v_14 L K H)
        (combined_lturn J A B C D E F G v_15 M L H)
        (combined_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      (lturn J A B C D E F G I L K H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn J A B C D E F G I L v_13 H)
        (combined_lturn J A B C D E F G M L K H)
        (step_lturn J A B C D E F G v_14 L K H)
        (combined_lturn J A B C D E F G v_15 M L H)
        (combined_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      (lturn J A B C D E F G I L K H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn J A B C D E F G I L v_13 H)
        (combined_lturn J A B C D E F G M L K H)
        (combined_lturn J A B C D E F G v_14 L K H)
        (step_lturn J A B C D E F G v_15 M L H)
        (combined_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      (lturn J A B C D E F G I L K H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn J A B C D E F G I L v_13 H)
        (combined_lturn J A B C D E F G M L K H)
        (combined_lturn J A B C D E F G v_14 L K H)
        (combined_lturn J A B C D E F G v_15 M L H)
        (step_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      (lturn J A B C D E F G I L K H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (step_lturn J A B C D E F G I L v_13 H)
        (combined_lturn J A B C D E F G M L K H)
        (combined_lturn J A B C D E F G v_14 L K H)
        (combined_lturn J A B C D E F G v_15 M L H)
        (combined_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      (lturn J A B C D E F G I L K H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (step_lturn I A B C D E F G K J L H)
        true
      )
      (step_lturn I A B C D E F G L K J H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (step_lturn__bar I A B C D E F G L J K H)
        true
      )
      (step_lturn I A B C D E F G L K J H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (v_12 (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn I A B C D E F G v_12 J L H)
        (step_lturn I A B C D E F G v_13 K J H)
        (combined_lturn I A B C D E F G v_14 L K H)
        (and (= v_12 I) (= v_13 I) (= v_14 I))
      )
      (step_lturn I A B C D E F G L K J H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (v_12 (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn I A B C D E F G v_12 J L H)
        (combined_lturn I A B C D E F G v_13 K J H)
        (step_lturn I A B C D E F G v_14 L K H)
        (and (= v_12 I) (= v_13 I) (= v_14 I))
      )
      (step_lturn I A B C D E F G L K J H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (v_12 (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) )
    (=>
      (and
        (step_lturn I A B C D E F G v_12 J L H)
        (combined_lturn I A B C D E F G v_13 K J H)
        (combined_lturn I A B C D E F G v_14 L K H)
        (and (= v_12 I) (= v_13 I) (= v_14 I))
      )
      (step_lturn I A B C D E F G L K J H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn J A B C D E F G I L v_13 H)
        (step_lturn J A B C D E F G M L K H)
        (combined_lturn J A B C D E F G v_14 L K H)
        (combined_lturn J A B C D E F G v_15 M L H)
        (combined_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      (step_lturn J A B C D E F G I L K H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn J A B C D E F G I L v_13 H)
        (combined_lturn J A B C D E F G M L K H)
        (step_lturn J A B C D E F G v_14 L K H)
        (combined_lturn J A B C D E F G v_15 M L H)
        (combined_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      (step_lturn J A B C D E F G I L K H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn J A B C D E F G I L v_13 H)
        (combined_lturn J A B C D E F G M L K H)
        (combined_lturn J A B C D E F G v_14 L K H)
        (step_lturn J A B C D E F G v_15 M L H)
        (combined_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      (step_lturn J A B C D E F G I L K H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn J A B C D E F G I L v_13 H)
        (combined_lturn J A B C D E F G M L K H)
        (combined_lturn J A B C D E F G v_14 L K H)
        (combined_lturn J A B C D E F G v_15 M L H)
        (step_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      (step_lturn J A B C D E F G I L K H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (step_lturn J A B C D E F G I L v_13 H)
        (combined_lturn J A B C D E F G M L K H)
        (combined_lturn J A B C D E F G v_14 L K H)
        (combined_lturn J A B C D E F G v_15 M L H)
        (combined_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      (step_lturn J A B C D E F G I L K H)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn J A B C D E F G I L v_13 H)
        (step_lturn J A B C D E F G I K L H)
        (combined_lturn J A B C D E F G M L K H)
        (combined_lturn J A B C D E F G v_14 L K H)
        (combined_lturn J A B C D E F G v_15 M L H)
        (combined_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (step_lturn J A B C D E F G I L v_13 H)
        (combined_lturn J A B C D E F G I K L H)
        (combined_lturn J A B C D E F G M L K H)
        (combined_lturn J A B C D E F G v_14 L K H)
        (combined_lturn J A B C D E F G v_15 M L H)
        (combined_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn J A B C D E F G I L v_13 H)
        (combined_lturn J A B C D E F G I K L H)
        (combined_lturn J A B C D E F G M L K H)
        (combined_lturn J A B C D E F G v_14 L K H)
        (combined_lturn J A B C D E F G v_15 M L H)
        (step_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn J A B C D E F G I L v_13 H)
        (combined_lturn J A B C D E F G I K L H)
        (combined_lturn J A B C D E F G M L K H)
        (combined_lturn J A B C D E F G v_14 L K H)
        (step_lturn J A B C D E F G v_15 M L H)
        (combined_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn J A B C D E F G I L v_13 H)
        (combined_lturn J A B C D E F G I K L H)
        (combined_lturn J A B C D E F G M L K H)
        (step_lturn J A B C D E F G v_14 L K H)
        (combined_lturn J A B C D E F G v_15 M L H)
        (combined_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) (v_15 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn J A B C D E F G I L v_13 H)
        (combined_lturn J A B C D E F G I K L H)
        (step_lturn J A B C D E F G M L K H)
        (combined_lturn J A B C D E F G v_14 L K H)
        (combined_lturn J A B C D E F G v_15 M L H)
        (combined_lturn J A B C D E F G I M L H)
        (and (= v_13 J) (= v_14 J) (= v_15 J))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (v_12 (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn I A B C D E F G v_12 J L H)
        (step_lturn I A B C D E F G L J K H)
        (combined_lturn I A B C D E F G v_13 K J H)
        (combined_lturn I A B C D E F G v_14 L K H)
        (and (= v_12 I) (= v_13 I) (= v_14 I))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (v_12 (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) )
    (=>
      (and
        (step_lturn I A B C D E F G v_12 J L H)
        (combined_lturn I A B C D E F G L J K H)
        (combined_lturn I A B C D E F G v_13 K J H)
        (combined_lturn I A B C D E F G v_14 L K H)
        (and (= v_12 I) (= v_13 I) (= v_14 I))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (v_12 (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn I A B C D E F G v_12 J L H)
        (combined_lturn I A B C D E F G L J K H)
        (combined_lturn I A B C D E F G v_13 K J H)
        (step_lturn I A B C D E F G v_14 L K H)
        (and (= v_12 I) (= v_13 I) (= v_14 I))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (v_12 (_ BitVec 32)) (v_13 (_ BitVec 32)) (v_14 (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn I A B C D E F G v_12 J L H)
        (combined_lturn I A B C D E F G L J K H)
        (step_lturn I A B C D E F G v_13 K J H)
        (combined_lturn I A B C D E F G v_14 L K H)
        (and (= v_12 I) (= v_13 I) (= v_14 I))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn I A B C D E F G L K J H)
        (step_lturn I A B C D E F G L J K H)
        true
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (step_lturn I A B C D E F G L K J H)
        (combined_lturn I A B C D E F G L J K H)
        true
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (combined_lturn__bar I A B C D E F G L K J H)
        (step_lturn I A B C D E F G L K J H)
        true
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) )
    (=>
      (and
        (step_lturn__bar I A B C D E F G L K J H)
        (combined_lturn I A B C D E F G L K J H)
        true
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) )
    (=>
      (and
        CHC_COMP_FALSE
      )
      false
    )
  )
)

(check-sat)
(exit)
