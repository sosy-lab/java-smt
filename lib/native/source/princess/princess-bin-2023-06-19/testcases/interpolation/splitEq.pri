\predicates {
  inSigned(int, int);
}

\functions {
  int x;
  \relational \partial int divSigned(int, int, int);
  \relational \partial int divUnsigned(int, int, int);
  \relational \partial int mulSigned(int, int, int);
  \partial \relational int mul(int, int);
  \partial \relational int div(int, int);
  \partial \relational int shiftLeft(int, int);
}

\problem {
  \forall int x; (inSigned(32, x) ->
    x >= -2*1024*1024*1024 & x < 2*1024*1024*1024)
&
  \forall int x; {shiftLeft(x, 32)}
    shiftLeft(x, 32) = 4*1024*1024*1024*x
&
  \forall int x; {mul(x, 0)} mul(x, 0) = 0
&
  \forall int x; {mul(x, -1)} mul(x, -1) = -x
&
  \forall int x, y, res; {mul(x, y)}
      ((y >= 1 | y <= -2) -> mul(x, y) = res ->
       \exists int l, n, subres; (
           mul(2*x, l) = subres &
           y = 2*l + n & (
             n = 0 & res = subres
             |
             n = 1 & res = subres + x
       )))
&
  \forall int x, y, res, width; {mulSigned(width, x, y)} (
    mulSigned(width, x, y) = res ->
    \exists int k; res = mul(x, y) + shiftLeft(k, width) &
    inSigned(width, res)
  )
&
  \forall int x, y, res; {div(x, y)} (
      y != 0 ->
      \exists int mulres; (
         mul(div(x, y), y) = mulres &
         mulres <= x & (mulres > x + y | mulres > x - y)
      )
  )
&
  \forall int x, y, res, width; {divSigned(width, x, y)} (
    divSigned(width, x, y) = res ->
    \exists int divres; (divres = div(x, y) &
                         (res = divres | res = divres - shiftLeft(1, width))) &
    inSigned(width, res)
  )

->
  \part[p0] (x >= -1000000 & x <= 10000000)
->
  \part[p1] divSigned(32, mulSigned(32, x, 10), 10) = x
}

\interpolant { p0; p1 }
