/**
 * The linear unification constraint
 *   f(X) = f(Y) & f(W) != f(Z) + X - Y
 *
 * (version that is more suited to +posUnitResolution)
 */


\functions {
        int f(int);
}

\problem {
  \exists int X, Y, Z, W;
    {f(X), f(Y), f(W), f(Z)}
    (f(X) = f(Y) & f(W) != f(Z) + X - Y)
}