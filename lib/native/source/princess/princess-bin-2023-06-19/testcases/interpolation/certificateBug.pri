\predicates {
  inSigned(int, int);
}

\functions {
  \relational \partial int addSigned(int, int, int);
  \relational \partial int mulSigned(int, int, int);
  \relational \partial int minusSigned(int, int);
}

\problem {
  \forall int x, y, res, base; {addSigned(base, x, y)} (
    addSigned(base, x, y) = res ->
    (x + y >= base -> res = x + y - 2*base) &
    (x + y < -base -> res = x + y + 2*base) &
    (x + y >= -base & x + y < base -> res = x + y)
  )
->
  \forall int base, x; {mulSigned(base, x, 0)} mulSigned(base, x, 0) = 0
&
  \forall int base, x; {mulSigned(base, x, -1)} mulSigned(base, x, -1) = minusSigned(base, x)
&
  \forall int base, x, y, res; {mulSigned(base, x, y)}
      ((y >= 1 | y <= -2) -> mulSigned(base, x, y) = res ->
       \exists int l, n, subres; (
           mulSigned(base, addSigned(base, x, x), l) = subres &
           y = 2*l + n & (
             n = 0 & res = subres
             |
                // HACK to prevent the "addSigned" from escaping
                // (should be fixed in the function encoder, TODO)
             n = 1 & \exists int x'; (x' = x & res = addSigned(base, subres, x'))
       )))
&
  \forall int base, x, res; {minusSigned(base, x)} (
    minusSigned(base, x) = res ->
    (-x >= base -> res = -x - 2*base) &
    (-x < base -> res = -x)
  )
&
  \forall int x, base; (inSigned(base, x) -> x >= -base & x < base)
->

\part[p0000] (((sym0<=127) & (addSigned(256, mulSigned(256, sym0, -1), sym1)>=1) & (sym0>=1) & !((sym2>0)))) &
\part[p0001] (false) &
\part[p0002] ((!((sym0<=127)) | !((addSigned(256, mulSigned(256, sym0, -1), sym1)>=1)) | !((sym0>=1)))) &
\part[p0000] inSigned(128, sym0) & 
\part[p0000] inSigned(128, sym1) & 
\part[p0000] inSigned(128, sym2)
-> false
}
\functions {
int sym0, sym1, sym2;
}

\interpolant{p0000;p0001,p0002}