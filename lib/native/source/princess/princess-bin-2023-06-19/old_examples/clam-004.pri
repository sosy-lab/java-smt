/**
@provable automatic

Examples taken from the paper
"A Framework for the Flexible Integration of a Class of
Decision Procedures into Theorem Provers",
Predrag Janicic, Alan Bundy, Ian Green
*/

\predicates {
	ms(int, int);
	mul(int, int, int);
}

\problem {
/*
// Totality
	\forall int x; \exists int y; ms(x, y)
->
	\forall int x, y; \exists int z; mul(x, y, z)
->
// Functionality
	\forall int x, y1, y2; (ms(x, y1) -> ms(x, y2) -> y1 = y2)
->
	\forall int x1, x2, y1, y2; (mul(x1, x2, y1) -> mul(x1, x2, y2) -> y1 = y2)
->
// mul-axioms (assocativity, commutativity)
	\forall int x, y, z, m1, m2, m3, m4;
	(mul(x, y, m1) -> mul(m1, z, m2) -> mul(y, z, m3) -> mul(x, m3, m4) -> m2 = m4)
->
	\forall int x, y, m1;
	(mul(x, y, m1) -> mul(y, x, m1))
->
*/
	\forall int i, j, ms_i, m; (ms(i, ms_i) -> mul(ms_i, j, m) -> j <= m)
->
	\forall int a, b, c, ms_a, ms_b, ms_c, mul_a_a, mul_a_a_a, mul_a_a_a_a, mul_b_b, mul_a_a_b;
	(ms(a, ms_a) -> ms(b, ms_b) -> ms(c, ms_c) ->
	 mul(ms_a, ms_a, mul_a_a) ->
	 mul(ms_a, mul_a_a, mul_a_a_a) ->
	 mul(ms_a, mul_a_a_a, mul_a_a_a_a) ->
	 mul(ms_b, ms_b, mul_b_b) ->
	 mul(ms_b, mul_a_a, mul_a_a_b) ->
	 ms_c + mul_a_a + mul_b_b <
	 ms_c + mul_b_b + 2*mul_a_a_b + mul_a_a_a_a)
}