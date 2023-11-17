\functions {
  bool f(bool);
}

\problem {
  f(true) = true
&
  f(false) = false
->
  \forall bool x; f(f(x)) = f(x)
&
  \forall bool x; f(x) = x
}
