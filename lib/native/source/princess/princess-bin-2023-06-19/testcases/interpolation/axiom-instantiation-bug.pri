\functions {
  \partial int f(int);
  int a, b, c;
}

\problem {
  \forall int x; {f(x)} f(x)=0
->
  \part[left] (a=f(3))
->
  \part[right] (!\exists int x; a=2*x)
->
  false
}

\interpolant{left; right}
