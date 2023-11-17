/*
 * This test case checks a previous bug in the function encoder,
 * where the trigger in the context of alternating quantifiers was
 * not handled correctly (and lead to an exception)
 */

\functions {
int null;
int S_select(int, int);
}
\problem {


\forall int x, y, z; S_select(S_select(x, y), z) = null

->

\forall int x, y; \exists int z; {S_select(S_select(x, y), z)} S_select(S_select(x, y), z) = null

}
