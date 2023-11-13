
(model
  (define-fun bla () (Array Int Int) ((as const (Array Int Int)) 0))
  (define-fun test () (Array (Array Int Int) (Array Int (_ BitVec 5))) (store ((as const (Array (Array Int Int) (Array Int (_ BitVec 5)))) ((as const (Array Int (_ BitVec 5))) (_ bv0 5))) ((as const (Array Int Int)) 0) ((as const (Array Int (_ BitVec 5))) (_ bv31 5))))
  (define-fun hi () (_ BitVec 5) (_ bv31 5))
)
