
\existentialConstants {
  int c;
}

\problem {
c + 245 >= 0
 &
\forall int x; (
  -1*c + 1 >= x
->
  246 >= x
->
  x >= 0
->
  \forall int y; (256*y + x + c + -1 != 0))
}
