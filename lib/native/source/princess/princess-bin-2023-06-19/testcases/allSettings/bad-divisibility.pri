\functions {
   int c;
}

\problem {
  \forall int x; (c >= 10*x + 1 & c <= 10*x + 9 -> false)
->
  \forall int x; (c != 10*x + 1 -> false)
}