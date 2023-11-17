\predicates {
  inArray(int);
  in32(int);
  inU32(int);
  inSigned(int, int);
  inUnsigned(int, int);
}

\functions {
  \relational \partial int addU(int, int, int);
  \relational \partial int addU32(int, int);
  \relational \partial int shiftLeft(int, int);
  \relational \partial int addSigned(int, int, int);
  \relational \partial int addUnsigned(int, int, int);

  int sym0, undef0, sym1, undef1, sym2, sym3, undef2, sym4, sym5, sym6, sym7;
}

\problem {
  \forall int x, y; {shiftLeft(x, y)} (
    y > 32 -> shiftLeft(x, y) = shiftLeft(4*1024*1024*1024*x, y-32))
&
  \forall int x; {shiftLeft(x, 32)}
    shiftLeft(x, 32) = 4*1024*1024*1024*x
&
  \forall int x; {shiftLeft(x, 31)}
    shiftLeft(x, 31) = 2*1024*1024*1024*x
&
  \forall int x, y; {shiftLeft(x, y)} (
    y < 31 & y > 0 -> shiftLeft(x, y) = shiftLeft(2*x, y-1))
&
  \forall int x; {shiftLeft(x, 0)} shiftLeft(x, 0) = x
&
  \forall int x, width; (inSigned(width, x) ->
    \exists int y; (y = shiftLeft(1, width - 1) & x >= -y & x < y))
&
  \forall int x, width; (inUnsigned(width, x) ->
    x >= 0 & x < shiftLeft(1, width))
&

  \forall int x, y, res, width; {addSigned(width, x, y)} (
    addSigned(width, x, y) = res ->
    \exists int k; res = x + y + shiftLeft(k, width) &
    inSigned(width, res)
  )
&

  \forall int x, y, res, width; {addUnsigned(width, x, y)} (
    addUnsigned(width, x, y) = res ->
    (res = x + y | res = x + y - shiftLeft(1, width)) &
    inUnsigned(width, res)
  )
&

\part[p0] (((sym0=undef0) & (sym1=undef1) & (sym2=0) & (sym3=undef2))) &
\part[p1] (true) &
\part[p2] ((sym4=0)) &
\part[p3] ((sym4<5)) &
\part[p4] (((sym5=addUnsigned(32, 1, sym4)) & (sym6=addUnsigned(32, 1, sym7)))) &
\part[p5] (true) &
\part[p6] (!((sym5<5))) &
\part[p7] (true) & 
\part[p0] inArray(sym0) & 
\part[p0] inArray(sym1) & 
\part[p0] inSigned(32, sym2) & 
\part[p0] inArray(sym3) & 
\part[p2] inUnsigned(32, sym4) & 
\part[p4] inUnsigned(32, sym5) & 
\part[p4] inUnsigned(32, sym6) & 
\part[p4] inUnsigned(32, sym7) & 
\part[p0] inArray(undef0) & 
\part[p0] inArray(undef1) & 
\part[p0] inArray(undef2)
->
false
}

\interpolant{p0;p1;p2;p3;p4;p5;p6;p7}
