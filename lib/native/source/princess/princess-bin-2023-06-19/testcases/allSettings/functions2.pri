
\functions {
	int a;
	int b;
}

\predicates {
	f(int,int);
	g(int,int);
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

// The problem
	\forall int x, y; ( g(x,y) -> f(y,y) )
&
	g(a, b)
->
	\forall int x; ( f(b, x) -> g(a, x) )
}
