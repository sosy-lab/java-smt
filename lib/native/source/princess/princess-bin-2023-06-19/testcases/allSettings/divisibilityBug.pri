// Case that previously led to an assertion failure: do not
// apply maxi-scoping for existential quantifiers that encode
// divisibilities

\existentialConstants {
  int a;
}

\problem {
  \exists int v0; (a=(-2*v0)) & ! \exists int v0; (a=(-2*v0))
}
