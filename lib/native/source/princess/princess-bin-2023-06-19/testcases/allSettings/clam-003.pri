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
	\forall int x, ms_x; (ms(x, ms_x) -> 0 < ms_x)
->
	\forall int i, j, m; (mul(i, j, m) -> 0 < i -> j <= m)
->
	\forall int a, b, c, ms_a, ms_b, ms_c, mul_a_a, mul_a_a_a_a, mul_b_b, mul_a_a_b;
	(ms(a, ms_a) -> ms(b, ms_b) -> ms(c, ms_c) ->
	 mul(ms_a, ms_a, mul_a_a) ->
	 mul(mul_a_a, mul_a_a, mul_a_a_a_a) ->
	 mul(ms_b, ms_b, mul_b_b) ->
	 mul(mul_a_a, ms_b, mul_a_a_b) ->
	 ms_c + mul_a_a + mul_b_b <
	 ms_c + mul_b_b + 2*mul_a_a_b + mul_a_a_a_a)
}