\predicates {
select(int,int,int);
store(int,int,int,int);
}

\functions {
int id1, id2, i1_0, j1_0, read1_0, write1_0, readRec1_0, writeRec1_0, i1_1, j1_1, read1_1, write1_1, readRec1_1, writeRec1_1, i1_2, j1_2, read1_2, write1_2, readRec1_2, writeRec1_2, i1_3, j1_3, read1_3, write1_3, readRec1_3, writeRec1_3, i2_0, j2_0, read2_0, write2_0, readRec2_0, writeRec2_0, A0, A1, A2, A3, i_check_1, j_check_1, read_check_1, write_check_1, readRec_check_1, writeRec_check_1, i_check_2, j_check_2, read_check_2, write_check_2, readRec_check_2, writeRec_check_2, A_check_1, A_check_2, all_54_0, all_54_1, all_54_2, all_54_3, all_54_4, all_54_5, all_67_0, all_67_1, all_67_2, all_76_0, all_76_1, all_76_2, all_85_0, all_85_1, all_85_2;
}

\problem {
! (all_54_3 + -1*A_check_2 = 0 & all_54_0 + -1*A_check_1 = 0 & j_check_2 + -1 = 0 & i_check_2 + -4*id2 = 0 & i_check_1 + -1*i1_3 = 0 & writeRec2_0 = 0 & readRec2_0 = 0 & j2_0 = 0 & i2_0 + -4*id2 = 0 & writeRec1_3 = 0 & readRec1_3 = 0 & id2 + -1*id1 != 0 & -1*j2_0 + 2 >= 0 & select(A_check_1, j_check_2 + i2_0, all_54_1) & select(A_check_1, j2_0 + i2_0, all_54_5) & select(A3, j_check_1 + i1_3, all_54_2) & select(A3, j1_3 + i1_3, all_54_4) & store(A_check_1, j2_0 + i2_0, all_54_5 + all_54_1, all_54_3) & store(A3, j1_3 + i1_3, all_54_4 + all_54_2, all_54_0) &
 ! \exists int x5; \exists int x4; \exists int x3; \exists int x2; \exists int x1; \exists int x0; (x3 + -1*x4 != 0 & select(x0, x3, x1) & store(x5, x4, x2, x0) & !select(x5, x3, x1)) &
 ! \exists int x4; \exists int x3; \exists int x2; \exists int x1; \exists int x0; (x1 + -1*x2 != 0 & select(x0, x3, x1) & store(x4, x3, x2, x0)) &
 ! \exists int x4; \exists int x3; \exists int x2; \exists int x1; \exists int x0; (x3 + -1*x4 != 0 & store(x0, x1, x2, x3) & store(x0, x1, x2, x4)) &

 ! \exists int x3; \exists int x2; \exists int x1; \exists int x0; (x2 + -1*x3 != 0 & select(x0, x1, x2) & select(x0, x1, x3)) &

 ! \forall int x5; \forall int x4; \forall int x3; \forall int x2; \forall int x1; \forall int x0; (! (x0 + -1*A_check_1 = 0 & x3 + -1*A_check_2 = 0 & i_check_2 + -4*id2 = 0 & i_check_1 + -1*i1_3 = 0 & writeRec2_0 = 0 & readRec2_0 = 0 & j2_0 = 0 & i2_0 + -4*id2 = 0 & writeRec1_3 = 0 & readRec1_3 = 0 & id2 + -1*id1 != 0 & select(A_check_1, j_check_2 + i2_0, x1) & select(A_check_1, j2_0 + i2_0, x5) & select(A3, j_check_1 + i1_3, x2) & select(A3, j1_3 + i1_3, x4) & store(A_check_1, j2_0 + i2_0, x1 + x5, x3) & store(A3, j1_3 + i1_3, x2 + x4, x0) & ! (j2_0 + -3 = 0 & j_check_2 != 0) & ! (j1_3 + -3 = 0 & j_check_1 != 0) & ! (j_check_2 + -1*j2_0 + -1 != 0 & -1*j2_0 + 2 >= 0) & ! (j_check_1 + -1*j1_3 + -1 != 0 & -1*j1_3 + 2 >= 0) & ! (! (writeRec_check_2 + -1*writeRec2_0 = 0 & write_check_2 + -1*write2_0 = 0) & ! (writeRec_check_2 + -1 = 0 & write_check_2 + -1*j2_0 + -1*i2_0 = 0)) & ! (! (writeRec_check_2 + -1 = 0 & write_check_2 + -1*write_check_1 = 0 & writeRec_check_1 + -1 = 0) & ! (writeRec_check_2 + -1 = 0 & write_check_2 + -1*read_check_1 = 0 & readRec_check_1 + -1 = 0)) & ! (! (readRec_check_2 + -1*readRec2_0 = 0 & read_check_2 + -1*read2_0 = 0) & ! (readRec_check_2 + -1 = 0 & ! (read_check_2 + -1*j_check_2 + -1*i2_0 != 0 & read_check_2 + -1*j2_0 + -1*i2_0 != 0))) & ! (! (writeRec_check_1 + -1*writeRec1_3 = 0 & write_check_1 + -1*write1_3 = 0) & ! (writeRec_check_1 + -1 = 0 & write_check_1 + -1*j1_3 + -1*i1_3 = 0)) & ! (! (readRec_check_1 + -1*readRec1_3 = 0 & read_check_1 + -1*read1_3 = 0) & ! (readRec_check_1 + -1 = 0 & ! (read_check_1 + -1*j_check_1 + -1*i1_3 != 0 & read_check_1 + -1*j1_3 + -1*i1_3 != 0))))) & ! (j2_0 + -3 = 0 & j_check_2 != 0) & ! (j1_3 + -3 = 0 & j_check_1 != 0) & ! (j_check_2 + -1*j2_0 + -1 != 0 & -1*j2_0 + 2 >= 0) & ! (j_check_1 + -1*j1_3 + -1 != 0 & -1*j1_3 + 2 >= 0) & ! (select(A_check_1, 4*id2 + 1, all_54_1) & store(A3, 4*id1 + 3, all_54_4 + all_54_2, A_check_1) & !select(A3, 4*id2 + 1, all_54_1)) & ! (select(A_check_1, 4*id2, all_54_5) & store(A3, 4*id1 + 3, all_54_4 + all_54_2, A_check_1) & !select(A3, 4*id2, all_54_5)) & ! (! (writeRec_check_2 + -1*writeRec2_0 = 0 & write_check_2 + -1*write2_0 = 0) & ! (writeRec_check_2 + -1 = 0 & write_check_2 + -1*j2_0 + -1*i2_0 = 0)) & ! (! (writeRec_check_2 + -1 = 0 & write_check_2 + -1*write_check_1 = 0 & writeRec_check_1 + -1 = 0) & ! (writeRec_check_2 + -1 = 0 & write_check_2 + -1*read_check_1 = 0 & readRec_check_1 + -1 = 0)) & ! (! (readRec_check_2 + -1*readRec2_0 = 0 & read_check_2 + -1*read2_0 = 0) & ! (readRec_check_2 + -1 = 0 & ! (read_check_2 + -1*j_check_2 + -1*i2_0 != 0 & read_check_2 + -1*j2_0 + -1*i2_0 != 0))) & ! (! (writeRec_check_1 + -1*writeRec1_3 = 0 & write_check_1 + -1*write1_3 = 0) & ! (writeRec_check_1 + -1 = 0 & write_check_1 + -1*j1_3 + -1*i1_3 = 0)) & ! (! (readRec_check_1 + -1*readRec1_3 = 0 & read_check_1 + -1*read1_3 = 0) & ! (readRec_check_1 + -1 = 0 & ! (read_check_1 + -1*j_check_1 + -1*i1_3 != 0 & read_check_1 + -1*j1_3 + -1*i1_3 != 0))))

|

/*
! (\forall int x3; (j1_3 + i1_3 + -4*id1 + -3 = 0 &
 ! (select(A3, 4*id1 + 3, x3) &
 ! \forall int x2; \forall int x1; \forall int x0; (! (4*x1 + -1*j_check_1 + -1*i1_3 = 0 &
 x1 + -1*id1 != 0 &
 i1_3 + -4*id1 != 0 &
 select(A3, j_check_1 + i1_3 + 1, x2) &
 select(A3, j_check_1 + i1_3, x0) &
 select(A3, j_check_1 + i1_3, all_54_2))))))
*/

 \exists int x5; \exists int x4; \exists int x3; (x5=all_54_2 &
! (j1_3 + i1_3 + -4*id1 + -3 = 0 &
 ! (select(A3, 4*id1 + 3, x3) &
 ! \forall int x2; \forall int x1; \forall int x0; (! (4*x1 + -1*x4 + -1*i1_3 = 0 &
    x1 + -1*id1 != 0 &
   i1_3 + -4*id1 != 0 &
   select(A3, x4 + i1_3 + 1, x2) &
   select(A3, x4 + i1_3, x0) &
   select(A3, x4 + i1_3, x5))))))
}
