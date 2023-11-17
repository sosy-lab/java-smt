


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

&	W != A
&	W != S
&	W != H
&	W != Y
&	W != O
&	W != U
&	W != R
&	W != N
&	W != D

&	A != S
&	A != H
&	A != Y
&	A != O
&	A != U
&	A != R
&	A != N
&	A != D

&	S != H
&	S != Y
&	S != O
&	S != U
&	S != R
&	S != N
&	S != D

&	H != Y
&	H != O
&	H != U
&	H != R
&	H != N
&	H != D

&	Y != O
&	Y != U
&	Y != R
&	Y != N
&	Y != D

&	O != U
&	O != R
&	O != N
&	O != D

&	U != R
&	U != N
&	U != D

&	R != N
&	R != D

&	N != D

&	            1000 * W + 100 * A + 10 * S + H
+	            1000 * Y + 100 * O + 10 * U + R
=	10000 * H + 1000 * A + 100 * N + 10 * D + S

-> false
}