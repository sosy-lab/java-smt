

\predicates {
	p(int);
}


\problem {
\forall int a; (
	\forall int x; p(2*x)
->
	\forall int x; !p(2*x+1)
->
	p(a)
->
	p(a+7)
)
}
