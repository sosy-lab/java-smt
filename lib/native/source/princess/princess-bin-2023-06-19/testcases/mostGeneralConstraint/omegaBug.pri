\existentialConstants {
  int I1, O1;
}

\predicates {
  in32(int);
  inU8(int);
}

\functions {
// Signed 32-bit arithmetic
  \partial \relational int addU8(int, int);
  \partial \relational int cast32(int);
}

\problem {
  \forall int x; (in32(x) -> x >= -2*1024*1024*1024 & x < 2*1024*1024*1024)
&
  \forall int x, res; {cast32(x)} (
    cast32(x) = res ->
    \exists int k; res = x + k * 4*1024*1024*1024 &
    in32(res)
  )
&
  \forall int x, y, res; {addU8(x, y)} (
    addU8(x, y) = res ->
    \exists int k; res = x + y + k * 256 &
    inU8(res)
  )
&
  \forall int x; (inU8(x) -> x >= 0 & x < 256)
->

  (O1 = addU8(I1,255)) & 
  (cast32(I1) != 0) & 
  (I1 = I1) & 
  inU8(I1)
->
  false
}