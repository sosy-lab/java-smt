/*
 * Example taken from "Equality and other theories",
 * p.230, Handbook of Tableaux Methods, Bernhard Beckert
 */

\functions {
	int a, b, c;
}

\predicates {
	f(int, int);
	g(int, int);
	p(int, int);
}

\problem {
// Totality
	\forall int x; \exists int y; f(x, y)
->
	\forall int x; \exists int y; g(x, y)
->
// Functionality
	\forall int x, y1, y2; (f(x, y1) -> f(x, y2) -> y1 = y2)
->
	\forall int x, y1, y2; (g(x, y1) -> g(x, y2) -> y1 = y2)
->

	\forall int x, a1; (
		f(x, a1)
	-> \exists int a2; (
		g(x, a2)
	&
		(a1=a2 | x!=a)
	))
->
	\forall int x, a1; (
		f(x, a1)
	-> 
		g(a1, x)
	)
->
	b = c
->
	\exists int a1, a2; (
		g(a, a1)
	&
		g(a1, a2)
	&
		p(a2, b)
	)
->
	!p(a, c)
->
	false
}