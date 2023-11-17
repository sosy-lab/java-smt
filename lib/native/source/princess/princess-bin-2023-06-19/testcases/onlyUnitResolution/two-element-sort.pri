\sorts {
  S;
}

\functions {
  S a, b;
  S f(S);
}

\problem {
  \forall S x; (x = a | x = b)
->
  \forall S x; f(f(x)) = x | \forall S x; f(f(x)) = f(x)
}
