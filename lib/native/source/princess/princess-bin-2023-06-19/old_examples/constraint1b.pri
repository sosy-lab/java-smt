/**
 * The linear unification constraint
 *   f(X) = f(Y) & f(W) != f(Z) + X - Y
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

	\forall int x, y, w, z;
	\forall int fx, fy, fw, fz; (
		f(x, fx)
	->
		f(y, fy)
	->
		f(w, fw)
	->
		f(z, fz)
	->
		!(fx = fy & fw != fz + x - y)
	)
->
	false
}