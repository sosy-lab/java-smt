(declare-fun |id#2@1| () (_ BitVec 32))
(declare-fun |id#0@1| () (_ BitVec 32))
(define-fun .10 () (_ BitVec 32) (_ bv10 32))
(define-fun .20 () (_ BitVec 32) |id#2@1|)
(define-fun .22 () Bool (bvslt .10 .20))
(define-fun .23 () Bool (not .22))
(define-fun .29 () (_ BitVec 1) (_ bv1 1))
(define-fun .30 () (_ BitVec 1) ((_ extract 31 31) .20))
(define-fun .31 () Bool (= .30 .29))
(define-fun .52 () Bool (not .31))
(define-fun .55 () (_ BitVec 32) |id#0@1|)
(define-fun .56 () Bool (bvslt .10 .55))
(define-fun .62 () Bool (not .56))
(define-fun .68 () (_ BitVec 1) ((_ extract 31 31) .55))
(define-fun .69 () Bool (= .68 .29))
(define-fun .89 () Bool (not .69))
(define-fun .92 () Bool (= .20 .55))
(define-fun .94 () Bool (and .52 .89))
(define-fun .101 () Bool (not .92))
(define-fun .103 () Bool (and .62 .94))
(define-fun .104 () Bool (and .101 .103))
(define-fun .105 () Bool (and .23 .104))
(assert .105)
(check-sat)
(get-model)