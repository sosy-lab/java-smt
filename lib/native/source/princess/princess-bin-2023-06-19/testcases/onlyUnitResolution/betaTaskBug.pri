\predicates {
  inArray(int);
  inSigned(int, int);
  inUnsigned(int, int);
  shiftLeft(int, int, int);
  addSigned(int, int, int, int);
  addUnsigned(int, int, int, int);
}

\problem {

\forall int x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10;
(! (x0 + -1*x8 = 0 & x1 + -1*x9 = 0 &
 x2 = 0 &
 x3 + -1*x10 = 0 &
 x4 = 0 &
 -1*x4 + 4 >= 0 &
 -1*x5 + 4 >= 0 &
 inUnsigned(32, x4) & inSigned(32, x2) &
 inArray(x0) & inArray(x1) & inArray(x3) & inArray(x8) &
 inArray(x9) & inArray(x10) &
 ! \exists int y0,y1,y2,y3; (addSigned(y0, y3, y2, y1) & ! (inSigned(y0, y1) & ! \forall int z0; (! (shiftLeft(1, y0, z0) & ! (z0 + -1*y1 + y2 + y3 != 0 & z0 + y1 + -1*y2 + -1*y3 != 0 & y1 + -1*y2 + -1*y3 != 0))))) &
 ! \exists int y0,y1,y2,y3; (addUnsigned(y0, y3, y2, y1) & ! (inUnsigned(y0, y1) & ! (y1 + -1*y2 + -1*y3 != 0 & !shiftLeft(1, y0, -1*y1 + y2 + y3)))) &
 ! \exists int y0,y1,y2,y3; (-1*y1 + 30 >= 0 & y1 + -1 >= 0 & shiftLeft(y2, y1, y0) & !shiftLeft(2*y2, y1 + -1, y0)) &
 ! \exists int y0,y1,y2,y3; (y1 + -33 >= 0 & shiftLeft(y2, y1, y0) & !shiftLeft(4294967296*y2, y1 + -32, y0)) &
 ! \exists int y0,y1,y2,y3; (y0 + -4294967296*y1 != 0 & shiftLeft(y1, 32, y0)) &
 ! \exists int y0,y1,y2,y3; (y0 + -2147483648*y1 != 0 & shiftLeft(y1, 31, y0)) &
 ! \exists int y0,y1,y2,y3; (y0 + -1*y1 != 0 & shiftLeft(y1, 0, y0)) &
 ! \exists int y0,y1,y2,y3; (inUnsigned(y0, y1) & ! (y1 >= 0 & ! \forall int z0; (! (z0 + -1*y1 + -1 >= 0 & shiftLeft(1, y0, z0))))) &
 !  ! \exists int y0,y1,y2,y3; (inSigned(y0, y1) & ! \exists int z0; (z0 + -1*y1 + -1 >= 0 & z0 + y1 >= 0 & shiftLeft(1, y0 + -1, z0))) &
 ! \forall int y0,y1; (! (y0 + -1*x6 = 0 & y1 + -1*x5 = 0 & addUnsigned(32, 1, x4, y1) & addUnsigned(32, 1, x7, y0) & inUnsigned(32, x5) & inUnsigned(32, x6) & inUnsigned(32, x7))) &
 ! (x5 + -1 = 0 & -1*x6 + 4294967295 >= 0)))

}
\functions {
int sym0, sym1, sym10, sym11, sym12, sym13, sym2, sym3, sym4, sym5, sym6, sym7, sym8, sym9, undef0, undef1, undef2;
}

