\problem {
  inSigned(128, x) & inSigned(512, y)
->
  subSigned(1024, addSigned(128, x, 1), y) = 13
->
  false
}
\functions {
  int x, y;
}
