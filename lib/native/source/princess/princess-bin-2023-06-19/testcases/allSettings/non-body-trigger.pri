\functions {
  int null;
  \partial int f(int, int);
}

\problem {
  \forall int x; { f(null, x) } f(x, null) = x
->
  f(null, null) = null + 1
->
  false
}