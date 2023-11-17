\existentialConstants {
  int a, b, c, d, z1, z2, z3;
}

\predicates {
  in32(int);
}

\functions {
  \partial int bitAdd32(int, int);
}

\problem {
  \forall int x; (in32(x) -> x >= -2*1024*1024*1024 & x < 2*1024*1024*1024)
->
  \forall int x, y, res; {bitAdd32(x, y)} (
    bitAdd32(x, y) = res ->
    \exists int k; res = x + y + k * 4*1024*1024*1024 &
    in32(res)
  )
->

  in32(a) & in32(b) & in32(c) & in32(d) &
  z1 = bitAdd32(a, 27) & z2 = bitAdd32(-1, b) & z3 = bitAdd32(5, z2)
->
  false
}