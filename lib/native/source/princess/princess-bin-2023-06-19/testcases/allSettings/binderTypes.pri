

\functions {
  int c, d;
}

\problem {
  (c >= d <-> \exists nat x; c = d + x)
&
  (c >= d <-> !\forall nat x; c != d + x)
&
  (c >= d <-> \exists nat x, y, z; c = d + x + y + z)
&
  (c >= d <-> \exists int[0, inf] x; c = d + x)
&
  (c <= d <-> \exists int[-inf, 0] x; c = d + x)
&
  (c > d + 2 <-> \exists int[1, inf] x, y, z; c = d + x + y + z)
&
  \forall int x; \exists (int y; int[0, 1] z) x = 2*y + z
&
  (\eps int[-1, 0] x; \exists int y; c + x = 2*y) >= -1
&
  ((\eps nat x; (c = d + x | d = c + x)) = 0 <-> c = d)
}