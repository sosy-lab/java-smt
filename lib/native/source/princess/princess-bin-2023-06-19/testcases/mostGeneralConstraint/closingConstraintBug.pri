\existentialConstants {
  int I1, O1;
}

\predicates {
  inU8(int);
  in32(int);
}

\functions {
  \partial \relational int cast32(int);
  \partial \relational int and(int, int);
  \partial \relational int andBit(int, int);
  \partial \relational int ones(int);
  \partial \relational int shiftLeft(int, int);
}

\problem {
  \forall int x, res; {cast32(x)} (
    cast32(x) = res ->
    \exists int k; res = x + k * 2*1000 &
    in32(res)
  )
&
  \forall int x; (in32(x) -> x >= -1000 & x < 1000)
&
  \forall int x; (inU8(x) -> x >= 0 & x < 8)
&
  \forall int x; {and(x, 0)} and(x, 0) = 0
&
  \forall int x; {and(x, -1)} and(x, -1) = x
&

  \forall int x, y, res; {and(x, y)}
      ((y >= 1 | y <= -2) -> and(x, y) = x)

&

  \forall int x, res; {ones(x)} (ones(x) = res ->
    x = 0 & res = 0
    |
    x = -1 & res = -1
    |
    (x > 0 | x < -1) &
    \exists int k; (
      x = 2*k & res = 0
      |
      x = 2*k + 1 & res = 1 + ones(k)
  ))

->
  ((I1 != 0)) & 
  (O1 = and(I1,cast32(I1)-1)) & 
  inU8(I1)
->
  false
}
