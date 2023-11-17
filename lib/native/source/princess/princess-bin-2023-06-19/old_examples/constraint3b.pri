/**
 * The linear unification constraint
 *   f(f(X)) = f(f(Y) + 1 + Z) & f(f(V)) = f(f(X) + 1 + W)    (Z >= 0, W >= 0)
 */


\predicates {
        f(int, int);
}

\problem {
// Totality
	\forall int x; \exists int y; f(x, y)
->
// Functionality
        \forall int x, y1, y2; (f(x, y1) -> f(x, y2) -> y1 = y2)
->
        \forall int x, y, z, v, w; (
        \forall int fx, fy, fv, ffx, ffv, ffyz, ffxw; (
		z >= 0 & w >= 0
	->
                f(x, fx)
        ->
                f(y, fy)
        ->
                f(v, fv)
        ->
                f(fx, ffx)
        ->
                f(fv, ffv)
        ->
                f(fy+1+z, ffyz)
        ->
                f(fx+1+w, ffxw)
        ->
                !(ffx = ffyz & ffv = ffxw)
        )
        )
->
	false
}
