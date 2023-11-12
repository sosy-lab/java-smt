
(model
  (define-fun bla () (Array Int Int) ((as const (Array Int Int)) 0))
  (define-fun test () (Array (Array Int Int) (Array Int Int)) (store ((as const (Array (Array Int Int) (Array Int Int))) (store ((as const (Array Int Int)) 0) 0 1)) ((as const (Array Int Int)) 0) (store ((as const (Array Int Int)) 7) 3 4)))
  (define-fun hi () Int 4)
)
