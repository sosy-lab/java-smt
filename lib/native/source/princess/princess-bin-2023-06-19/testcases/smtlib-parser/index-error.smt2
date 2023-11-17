(declare-const SP0 (_ BitVec 32))
(declare-const S0 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H0 (Array (_ BitVec 32) (_ BitVec 32)))

(declare-const SP1 (_ BitVec 32))
(declare-const S1 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H1 (Array (_ BitVec 32) (_ BitVec 32)))

(declare-const SP2 (_ BitVec 32))
(declare-const S2 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H2 (Array (_ BitVec 32) (_ BitVec 32)))

(declare-const SP3 (_ BitVec 32))
(declare-const S3 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H3 (Array (_ BitVec 32) (_ BitVec 32)))

(declare-const SP4 (_ BitVec 32))
(declare-const S4 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H4 (Array (_ BitVec 32) (_ BitVec 32)))

(declare-const SP5 (_ BitVec 32))
(declare-const S5 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H5 (Array (_ BitVec 32) (_ BitVec 32)))

(declare-const SP6 (_ BitVec 32))
(declare-const S6 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H6 (Array (_ BitVec 32) (_ BitVec 32)))

(declare-const SP7 (_ BitVec 32))
(declare-const S7 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H7 (Array (_ BitVec 32) (_ BitVec 32)))

(declare-const SP8 (_ BitVec 32))
(declare-const S8 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H8 (Array (_ BitVec 32) (_ BitVec 32)))

(declare-const SP9 (_ BitVec 32))
(declare-const S9 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H9 (Array (_ BitVec 32) (_ BitVec 32)))

(declare-const SP10 (_ BitVec 32))
(declare-const S10 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H10 (Array (_ BitVec 32) (_ BitVec 32)))

(declare-const SP11 (_ BitVec 32))
(declare-const S11 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H11 (Array (_ BitVec 32) (_ BitVec 32)))

(declare-const SP12 (_ BitVec 32))
(declare-const S12 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H12 (Array (_ BitVec 32) (_ BitVec 32)))

(declare-const SP13 (_ BitVec 32))
(declare-const S13 (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const H13 (Array (_ BitVec 32) (_ BitVec 32)))

(assert (= SP1 (bvadd SP0 #x00000001)))
(assert (forall ((x (_ BitVec 32))) (=> (not (= x SP0)) (= (select S1 x) (select S0 x)))))
(assert (= H1 H0))
(assert (= (select S1 SP0) #x0000000a))

(assert (= SP2 (bvadd SP1 #x00000001)))
(assert (forall ((x (_ BitVec 32))) (=> (not (= x SP1)) (= (select S2 x) (select S1 x)))))
(assert (= H2 H1))
(assert (= (select S2 SP1) (select S1 (bvsub SP1 #x00000001))))

(assert (= SP3 SP2))
(assert (forall ((x (_ BitVec 32))) (=> (not (= x (bvsub SP2 #x00000001))) (= (select S3 x) (select S2 x)))))
(assert (= H3 H2))
(assert (= (select S3 (bvsub SP3 #x00000001)) (select H2 (select S2 (bvsub SP2 #x00000001)))))

(assert (= SP4 (bvadd SP3 #x00000001)))
(assert (forall ((x (_ BitVec 32))) (=> (not (= x SP3)) (= (select S4 x) (select S3 x)))))
(assert (= H4 H3))
(assert (= (select S4 SP3) #x00000000))

(assert (= SP5 (bvsub SP4 #x00000002)))
(assert (forall ((x (_ BitVec 32))) (=> (and (not (= x SP5)) (not (= x (bvadd SP5 #x00000001))) (= (select S5 x) (select S4 x)))))


(assert (forall ((x (_ BitVec 32))) (=> (and (not (= x SP6)) (not (= x (bvadd SP6 #x00000001))) (= (select S6 x) (select S5 x)))))



