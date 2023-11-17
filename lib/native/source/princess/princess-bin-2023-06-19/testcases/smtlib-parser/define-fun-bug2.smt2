; In this example, the defined function is not inlined
; (because its body is too large); it is important to not define
; the introduced function x as "relational", since otherwise
; the problem becomes sat

(set-logic QF_BV)

(declare-fun b () Bool)

(define-fun x () (_ BitVec 8)
   (ite b (_ bv0 8)
   (ite b (_ bv1 8)
   (ite b (_ bv2 8)
   (ite b (_ bv3 8)
   (ite b (_ bv4 8)
   (ite b (_ bv5 8)
   (ite b (_ bv6 8)
   (ite b (_ bv7 8)
   (ite b (_ bv8 8)
   (ite b (_ bv9 8)
   (ite b (_ bv10 8)
   (ite b (_ bv11 8)
   (ite b (_ bv12 8)
   (ite b (_ bv13 8)
   (ite b (_ bv14 8)
   (ite b (_ bv15 8)
   (ite b (_ bv16 8)
   (ite b (_ bv17 8)
   (ite b (_ bv18 8)
   (ite b (_ bv19 8)
   (ite b (_ bv20 8)
   (ite b (_ bv21 8)
   (ite b (_ bv22 8)
   (_ bv23 8)))))))))))))))))))))))))

(assert (= x (_ bv30 8)))
(check-sat)
