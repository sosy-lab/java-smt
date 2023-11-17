


\functions {
	int W; int A; int S; int H; int Y; int O; int U; int R; int N; int D;
}


\problem {
	0 <= W & W <= 9
&	0 <= A & A <= 9
&	0 <= S & S <= 9
&	0 <= H & H <= 9
&	0 <= Y & Y <= 9
&	0 <= O & O <= 9
&	0 <= U & U <= 9
&	0 <= R & R <= 9
&	0 <= N & N <= 9
&	0 <= D & D <= 9

&	            1000 * W + 100 * A + 10 * S + H
+	            1000 * Y + 100 * O + 10 * U + R
=	10000 * H + 1000 * A + 100 * N + 10 * D + S

-> false
}