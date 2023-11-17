/**
 * Example taken from the 1960 paper by Davis and Putnam
 */

\predicates {
	F(int, int);
	G(int, int);
}

\problem {
	\exists int x, y; \forall int z; (
		(F(x,y) -> F(y,z) & F(z,z))
	&
		(F(x,y) & G(x,y) -> G(x,z) & G(z,z))
	)
}