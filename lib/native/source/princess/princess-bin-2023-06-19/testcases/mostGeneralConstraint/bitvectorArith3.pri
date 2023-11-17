\existentialConstants {
  int a, b, z;
}

\predicates {
  in32(int);
}

\functions {
  \partial int bitAdd32(int, int);
  \partial int shiftLeft32(int, int);
}

\problem {
  \forall int x; {shiftLeft32(x, 0)} shiftLeft32(x, 0) = x
->
  \forall int x, y, res; {shiftLeft32(x, y)}
      (y > 0 -> shiftLeft32(x, y) = res ->
       \exists int k; res = shiftLeft32(x, y-1) * 2 + k * 4*1024*1024*1024 &
       in32(res))
->
  \forall int x; (in32(x) -> x >= -2*1024*1024*1024 & x < 2*1024*1024*1024)
->
  \forall int x, y, res; {bitAdd32(x, y)} (
    bitAdd32(x, y) = res ->
    \exists int k; res = x + y + k * 4*1024*1024*1024 &
    in32(res)
  )
->

  in32(a) & in32(b) & // a >= 0 &
  z = shiftLeft32(bitAdd32(a, 1), 1)
->
  false
}