/**
 * The linear unification constraint
 *   f(f(X)) = f(f(Y)+1+Z)    (Z >= 0)
 */


\functions {
        int a, b;
        int f(int);
}

\problem {
  f(0) = a
->
  f(1) = b
->
  \exists int X, Y, Z;
    {f(X), f(f(Y)+1+Z)}
    (Z >= 0 & f(f(X)) = f(f(Y)+1+Z))
}