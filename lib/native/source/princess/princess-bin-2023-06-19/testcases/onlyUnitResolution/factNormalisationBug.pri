\predicates {
  inSigned(int, int);
  inUnsigned(int, int);
}

\functions {
  \relational \partial int addUnsigned(int, int, int);
  \partial \relational int and(int, int);
}

\problem {
  \forall int x; (inSigned(32, x) ->
    x >= -2*1024*1024*1024 & x < 2*1024*1024*1024)
&
  \forall int x; (inUnsigned(32, x) ->
    x >= 0 & x < 4*1024*1024*1024)
&
  \forall int x, y, res; {addUnsigned(32, x, y)} (
    addUnsigned(32, x, y) = res ->
    (res = x + y | res = x + y - 4*1024*1024*1024) &
    res >= 0 & res < 4*1024*1024*1024
  )
&
  \forall int x; {and(x, 0)} and(x, 0) = 0
&
  \forall int x; {and(x, -1)} and(x, -1) = x
&
  \forall int x, y, res; {and(x, y)}
      ((y >= 1 | y <= -2) -> and(x, y) = res ->
       \exists int k, l, m, n, subres; (
           and(k, l) = subres &
           x = 2*k + m & y = 2*l + n & m >= 0 & m <= 1 & (
             n = 0 & res = subres * 2
             |
             n = 1 & res = subres * 2 + m
       )))


->
\part[p0000] (true) &
\part[p0001] (((sym0<=268435456) & (sym0>=1))) &
\part[p0002] (true) &
\part[p0003] (((sym1<10) & (sym2=sym1))) &
\part[p0004] ((sym2!=0)) &
\part[p0005] ((sym3=and(addUnsigned(32, 4294967295, sym2), sym2))) &
\part[p0006] (!((sym1>=sym3))) &
\part[p0001] inSigned(32, sym0) & 
\part[p0003] inUnsigned(32, sym1) & 
\part[p0003] inUnsigned(32, sym2) & 
\part[p0005] inUnsigned(32, sym3)
-> false
}
\functions {
int sym0, sym1, sym2, sym3;
}
