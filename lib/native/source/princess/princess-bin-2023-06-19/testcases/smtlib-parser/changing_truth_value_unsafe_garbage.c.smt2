(set-info :origin "SLAyer refinement benchmarks created by Jael Kriener")
(set-logic HORN)
(declare-fun transition-2
             (Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int)
             Bool)
(declare-fun transition-3
             (Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int)
             Bool)
(assert (forall ((?A Int) (?B Int) (?C Int) (?D Int) (?E Int) (?F Int) (?G Int) (?H Int) (?I Int) (?J Int) (?K Int) (?L Int) (?M Int) (?N Int) (?O Bool) (?P Bool) (?Q Bool) (?R Bool) (?S Bool) (?T Bool) (?U Bool) (?V Int) (?W Int) (?X Int) (?Y Int) (?Z Int) (?A1 Int) (?B1 Int) (?C1 Int) (?D1 Int) (?E1 Int) (?F1 Int) (?G1 Int) (?H1 Int) (?I1 Int) (?J1 Int) (?K1 Int) (?L1 Bool) (?M1 Bool) (?N1 Bool) (?O1 Bool) (?P1 Bool) (?Q1 Bool) (?R1 Bool) (?S1 Bool) (?T1 Int) (?U1 Int) (?V1 Int) (?W1 Int) (?X1 Int) (?Y1 Int) (?Z1 Int) (?A2 Int) (?B2 Int) (?C2 Int) (?D2 Int) (?E2 Int) (?F2 Int) (?G2 Int) (?H2 Int) (?I2 Int) (?J2 Bool) (?K2 Bool) (?L2 Bool) (?M2 Bool) (?N2 Bool) (?O2 Bool) (?P2 Bool) (?Q2 Bool) (?R2 Int) (?S2 Int) (?T2 Int) (?U2 Int) (?V2 Int) (?W2 Int) (?X2 Int) (?Y2 Int) (?Z2 Int) (?A3 Int) (?B3 Int) (?C3 Int) (?D3 Int) (?E3 Int) (?F3 Int) (?G3 Int) (?H3 Bool) (?I3 Bool) (?J3 Bool) (?K3 Bool) (?L3 Bool) (?M3 Bool) (?N3 Bool) (?O3 Bool) (?P3 Int) (?Q3 Int) (?R3 Int) (?S3 Int) (?T3 Int) (?U3 Int) (?V3 Int) (?W3 Int) (?X3 Int) (?Y3 Int) (?Z3 Int) (?A4 Int) (?B4 Int) (?C4 Int) (?D4 Int) (?E4 Int) (?F4 Bool) (?G4 Bool) (?H4 Bool) (?I4 Bool) (?J4 Bool) (?K4 Bool) (?L4 Bool) (?M4 Bool) (?N4 Int) (?O4 Int) (?P4 Int) (?Q4 Int) (?R4 Int) (?S4 Int) (?T4 Int) (?U4 Int) (?V4 Int) (?W4 Int) (?X4 Int) (?Y4 Int) (?Z4 Int) (?A5 Int) (?B5 Int) (?C5 Int) (?D5 Bool) (?E5 Bool) (?F5 Bool) (?G5 Bool) (?H5 Bool) (?I5 Bool) (?J5 Bool) (?K5 Bool) (?L5 Int) (?M5 Int) (?N5 Int) (?O5 Int) (?P5 Int) (?Q5 Int) (?R5 Int) (?S5 Int) (?T5 Int) (?U5 Int) (?V5 Int) (?W5 Int) (?X5 Int) (?Y5 Int) (?Z5 Int) (?A6 Int) (?B6 Bool) (?C6 Bool) (?D6 Bool) (?E6 Bool) (?F6 Bool) (?G6 Bool) (?H6 Bool) (?I6 Bool) (?J6 Int) (?K6 Int) (?L6 Int) (?M6 Int) (?N6 Int) (?O6 Int) (?P6 Int) (?Q6 Int) (?R6 Int) (?S6 Int) (?T6 Bool) (?U6 Bool) (?V6 Bool) (?W6 Bool) (?X6 Bool) (?Y6 Bool) )(let (($x2880 (|transition-3| 1027 ?Q6 ?S6 ?O6 ?N6 ?M6 ?L6 ?K6 ?J6 ?P6 ?Z5 ?Y5 ?X5 ?W5 ?V5 ?W4 ?V4 ?U4 ?T4 ?S4 ?R4 ?Q4 ?P4 ?O4 ?N4 ?E4 ?D4 ?C4 ?B4 ?A4 ?Z3 ?Y3 ?X3 ?W3 ?V3 ?U3 ?T3 ?S3 ?R3 false ?Q2 ?P2 ?O2 ?N2 ?M2 ?L2 ?K2 ?J2 ?S1 ?R1 ?Q1 ?P1 ?O1 ?N1 ?M1 ?L1 ?U ?T ?S ?R ?Q ?P ?O ?E1 ?D1 ?C1 ?B1 ?A1 ?Z ?Y ?X ?W ?V ?N ?M ?L ?K ?J ?I ?H ?G ?F ?E ?D ?C ?B ?A)))
(let (($x14544 (= ?C6 ?H4)))
(let (($x11285 (= ?D6 ?I4)))
(let (($x19961 (= ?E6 ?J4)))
(let (($x934 (= ?F6 ?K4)))
(let (($x3415 (= ?G6 ?L4)))
(let (($x13197 (= ?H6 ?M4)))
(let (($x11951 (ite (and (<= ?P6 23) (not (<= (+ ?P6 (div ?J6 4)) 23))) (= ?A (div ?J6 4)) (= ?A ?F1))))
(let (($x6724 (ite (and (<= ?P6 22) (not (<= (+ ?P6 (div ?J6 4)) 22))) (= ?B (div ?J6 4)) (= ?B ?G1))))
(let (($x7438 (ite (and (<= ?P6 21) (not (<= (+ ?P6 (div ?J6 4)) 21))) (= ?C (div ?J6 4)) (= ?C ?H1))))
(let (($x9348 (ite (and (<= ?P6 20) (not (<= (+ ?P6 (div ?J6 4)) 20))) (= ?D (div ?J6 4)) (= ?D ?I1))))
(let (($x2766 (ite (and (<= ?P6 19) (not (<= (+ ?P6 (div ?J6 4)) 19))) (= ?E (div ?J6 4)) (= ?E ?J1))))
(let (($x23208 (ite (and (<= ?P6 18) (not (<= (+ ?P6 (div ?J6 4)) 18))) (= ?F (div ?J6 4)) (= ?F ?K1))))
(let (($x15604 (ite (and (<= ?P6 17) (not (<= (+ ?P6 (div ?J6 4)) 17))) (= ?G (div ?J6 4)) (= ?G ?T1))))
(let (($x11557 (ite (and (<= ?P6 16) (not (<= (+ ?P6 (div ?J6 4)) 16))) (= ?H (div ?J6 4)) (= ?H ?U1))))
(let (($x8579 (and (<= ?P6 15) (not (<= (+ ?P6 (div ?J6 4)) 15)))))
(let (($x17898 (and (<= ?P6 14) (not (<= (+ ?P6 (div ?J6 4)) 14)))))
(let (($x5091 (and (<= ?P6 13) (not (<= (+ ?P6 (div ?J6 4)) 13)))))
(let (($x6907 (and (<= ?P6 12) (not (<= (+ ?P6 (div ?J6 4)) 12)))))
(let (($x11789 (and (<= ?P6 11) (not (<= (+ ?P6 (div ?J6 4)) 11)))))
(let (($x22868 (and (<= ?P6 10) (not (<= (+ ?P6 (div ?J6 4)) 10)))))
(let (($x11726 (and (<= ?P6 9) (not (<= (+ ?P6 (div ?J6 4)) 9)))))
(let (($x4257 (and (<= ?P6 8) (not (<= (+ ?P6 (div ?J6 4)) 8)))))
(let (($x7824 (and (<= ?P6 7) (not (<= (+ ?P6 (div ?J6 4)) 7)))))
(let (($x8262 (and (<= ?P6 6) (not (<= (+ ?P6 (div ?J6 4)) 6)))))
(let (($x984 (and (<= ?P6 5) (not (<= (+ ?P6 (div ?J6 4)) 5)))))
(let (($x11468 (and (<= ?P6 4) (not (<= (+ ?P6 (div ?J6 4)) 4)))))
(let (($x12406 (and (<= ?P6 3) (not (<= (+ ?P6 (div ?J6 4)) 3)))))
(let (($x20811 (and (<= ?P6 2) (not (<= (+ ?P6 (div ?J6 4)) 2)))))
(let (($x11736 (and (<= ?P6 1) (not (<= (+ ?P6 (div ?J6 4)) 1)))))
(let (($x1835 (and (<= ?P6 0) (not (<= (+ ?P6 (div ?J6 4)) 0)))))
(let (($x15370 (ite (and (<= ?P6 23) (not (<= (+ ?P6 (div ?J6 4)) 23))) ?O (= ?O ?H3))))
(let (($x20709 (ite (and (<= ?P6 22) (not (<= (+ ?P6 (div ?J6 4)) 22))) ?P (= ?P ?I3))))
(let (($x22541 (ite (and (<= ?P6 21) (not (<= (+ ?P6 (div ?J6 4)) 21))) ?Q (= ?Q ?J3))))
(let (($x10983 (ite (and (<= ?P6 20) (not (<= (+ ?P6 (div ?J6 4)) 20))) ?R (= ?R ?K3))))
(let (($x17235 (ite (and (<= ?P6 19) (not (<= (+ ?P6 (div ?J6 4)) 19))) ?S (= ?S ?L3))))
(let (($x8871 (ite (and (<= ?P6 18) (not (<= (+ ?P6 (div ?J6 4)) 18))) ?T (= ?T ?M3))))
(let (($x11562 (ite (and (<= ?P6 17) (not (<= (+ ?P6 (div ?J6 4)) 17))) ?U (= ?U ?N3))))
(let (($x11838 (ite (and (<= ?P6 16) (not (<= (+ ?P6 (div ?J6 4)) 16))) ?L1 (= ?L1 ?O3))))
(let (($x18844 (not $x1835)))
(let ((?x15488 (div ?J6 4)))
(let ((?x3270 (+ ?P6 ?x15488)))
(let (($x15664 (<= ?x3270 64)))
(let (($x21951 (|transition-2| 1026 ?R6 ?P6 ?O6 ?N6 ?M6 ?L6 ?K6 ?J6 ?A6 ?Z5 ?Y5 ?X5 ?W5 ?V5 ?U5 ?T5 ?S5 ?R5 ?Q5 ?P5 ?O5 ?N5 ?M5 ?L5 ?C5 ?B5 ?A5 ?Z4 ?Y4 ?X4 false ?Y6 ?X6 ?W6 ?V6 ?U6 ?T6 ?I6 ?H6 ?G6 ?F6 ?E6 ?D6 ?C6 ?B6 ?K5 ?Q3 ?P3 ?G3 ?F3 ?E3 ?D3 ?C3 ?B3 ?A3 ?Z2 ?Y2 ?X2 ?W2 ?V2 ?U2 ?T2)))
(let (($x14153 (and $x21951 $x15664 $x18844 (ite $x11736 ?Q2 (= ?Q2 ?J5)) (ite $x20811 ?P2 (= ?P2 ?I5)) (ite $x12406 ?O2 (= ?O2 ?H5)) (ite $x11468 ?N2 (= ?N2 ?G5)) (ite $x984 ?M2 (= ?M2 ?F5)) (ite $x8262 ?L2 (= ?L2 ?E5)) (ite $x7824 ?K2 (= ?K2 ?D5)) (ite $x4257 ?J2 (= ?J2 ?M4)) (ite $x11726 ?S1 (= ?S1 ?L4)) (ite $x22868 ?R1 (= ?R1 ?K4)) (ite $x11789 ?Q1 (= ?Q1 ?J4)) (ite $x6907 ?P1 (= ?P1 ?I4)) (ite $x5091 ?O1 (= ?O1 ?H4)) (ite $x17898 ?N1 (= ?N1 ?G4)) (ite $x8579 ?M1 (= ?M1 ?F4)) $x11838 $x11562 $x8871 $x17235 $x10983 $x22541 $x20709 $x15370 (ite $x1835 (= ?E1 ?x15488) (= ?E1 ?S2)) (ite $x11736 (= ?D1 ?x15488) (= ?D1 ?R2)) (ite $x20811 (= ?C1 ?x15488) (= ?C1 ?I2)) (ite $x12406 (= ?B1 ?x15488) (= ?B1 ?H2)) (ite $x11468 (= ?A1 ?x15488) (= ?A1 ?G2)) (ite $x984 (= ?Z ?x15488) (= ?Z ?F2)) (ite $x8262 (= ?Y ?x15488) (= ?Y ?E2)) (ite $x7824 (= ?X ?x15488) (= ?X ?D2)) (ite $x4257 (= ?W ?x15488) (= ?W ?C2)) (ite $x11726 (= ?V ?x15488) (= ?V ?B2)) (ite $x22868 (= ?N ?x15488) (= ?N ?A2)) (ite $x11789 (= ?M ?x15488) (= ?M ?Z1)) (ite $x6907 (= ?L ?x15488) (= ?L ?Y1)) (ite $x5091 (= ?K ?x15488) (= ?K ?X1)) (ite $x17898 (= ?J ?x15488) (= ?J ?W1)) (ite $x8579 (= ?I ?x15488) (= ?I ?V1)) $x11557 $x15604 $x23208 $x2766 $x9348 $x7438 $x6724 $x11951 (= ?U5 ?W4) (= ?T5 ?V4) (= ?S5 ?U4) (= ?R5 ?T4) (= ?Q5 ?S4) (= ?P5 ?R4) (= ?O5 ?Q4) (= ?N5 ?P4) (= ?M5 ?O4) (= ?L5 ?N4) (= ?C5 ?E4) (= ?B5 ?D4) (= ?A5 ?C4) (= ?Z4 ?B4) (= ?Y4 ?A4) (= ?X4 ?Z3) (= ?Y6 ?J5) (= ?X6 ?I5) (= ?W6 ?H5) (= ?V6 ?G5) (= ?U6 ?F5) (= ?T6 ?E5) (= ?I6 ?D5) $x13197 $x3415 $x934 $x19961 $x11285 $x14544 (= ?B6 ?G4) (= ?K5 ?F4) (= ?Q3 ?S2) (= ?P3 ?R2) (= ?G3 ?I2) (= ?F3 ?H2) (= ?E3 ?G2) (= ?D3 ?F2) (= ?C3 ?E2) (= ?B3 ?D2) (= ?A3 ?C2) (= ?Z2 ?B2) (= ?Y2 ?A2) (= ?X2 ?Z1) (= ?W2 ?Y1) (= ?V2 ?X1) (= ?U2 ?W1) (= ?S6 ?x3270) (= ?T2 ?V1))))
(=> $x14153 $x2880)))))))))))))))))))))))))))))))))))))))))))))))
)
(check-sat)
