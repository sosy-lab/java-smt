/*
 * Example taken from "Equality and other theories",
 * p. 241, Handbook of Tableaux Methods, Bernhard Beckert
 */

\functions {
	int tr;
}

\predicates {
	i(int, int, int);
}

\problem {
// Totality
	\forall int x1, x2; \exists int y; i(x1, x2, y)
->
// Functionality
	\forall int x1, x2, y1, y2; (i(x1, x2, y1) -> i(x1, x2, y2) -> y1 = y2)
->

	\forall int x; i(tr, x, x)
->
	\forall int x, y, z; \exists int a1, a2, a3, a4; (
		i(x, y, a1)
	&
		i(y, z, a2)
	&
		i(x, z, a3)
	&
		i(a2, a3, a4)
	&
		i(a1, a4, tr)
	)
->
	\forall int x, y; \exists int a1, a2, a3; (
		i(x, y, a1)
	&
		i(a1, y, a2)
	&
		i(y, x, a3)
	&
		i(a3, x, a2)
	)
->
	\forall int x, y, z; \forall int a1, a2, a3; (
		i(z, y, a1)
	->
		i(y, a1, a2)
	->
		i(x, a2, a3)
	->
		a3=tr
	)

/*	
\forall int x, y, z, a1; (
		i(z, y, a1)
	-> \exists int w; (
		i(x, w, tr)
	&
		i(y, a1, w)
	))
*/
//	\forall int x; (i(tr, tr, x) -> x=tr)
}