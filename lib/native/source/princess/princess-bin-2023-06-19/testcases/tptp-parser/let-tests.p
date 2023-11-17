
tff(uni, type, uni: $tType).

tff(deco, type, deco: $tType).

tff(ty, type, ty: $tType).

tff(sort, type, sort: (ty * uni) > deco).

tff(my_int, type, my_int: ty).

tff(my_real, type, my_real: ty).

tff(my_bool, type, my_bool: $tType).

tff(bool1, type, bool1: ty).

tff(true, type, true: my_bool).

tff(false, type, false: my_bool).

tff(match_bool, type, match_bool: (my_bool * deco * deco) > uni).

tff(match_bool_True, axiom, ![A:ty]: ![Z:uni, Z1:uni]: (sort(A,
  match_bool(true, sort(A, Z), sort(A, Z1))) = sort(A, Z))).

tff(match_bool_False, axiom, ![A:ty]: ![Z:uni, Z1:uni]: (sort(A,
  match_bool(false, sort(A, Z), sort(A, Z1))) = sort(A, Z1))).

tff(true_False, axiom, ~ ((true = false))).

tff(bool_inversion, axiom, ![U:my_bool]: ((U = true) | (U = false))).

tff(tuple0, type, tuple0: $tType).

tff(tuple01, type, tuple01: ty).

tff(tuple02, type, tuple02: tuple0).

tff(tuple0_inversion, axiom, ![U:tuple0]: (U = tuple02)).

tff(compatOrderMult, axiom, ![X:$int, Y:$int, Z:$int]: ($lesseq(X,Y)
  => ($lesseq(0,Z) => $lesseq($product(X,Z),$product(Y,Z))))).

tff(o_type,type, o: $int).
tff(o1_type,type, o1: $int).

tff(wP_parameter_f91, conjecture, ![N:$int]: ($lesseq(N,100) => $let_tf(o =
  $sum(N,11), $let_tf(o1 = $ite_t($lesseq(o,100), 91, $difference(o,10)),
  ($lesseq(0,$difference(101,N))
  & $less($difference(101,o1),$difference(101,N))))))).

