/**
 * The linear unification constraint
 *   f(f(X)) = f(f(Y)+1+Z)    (Z >= 0)
 *
 * (version that is more suited to +posUnitResolution)
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

        \forall int x, y, z; (
        \forall int fx, fy, ffx, ffyz; (
		z >= 0
	->
                f(x, fx)
        ->
                f(y, fy)
        ->
                f(fx, ffx)
        ->
                f(fy+1+z, ffyz)
        ->
                ffx != ffyz
        )
        )
->
	false
}