%------------------------------------------------------------------------------
% File     : ARI620=1 : TPTP v5.3.0. Released v5.1.0.
% Domain   : Arithmetic
% Problem  : 8 is a power of 2
% Version  : Especial.
% English  :

% Refs     : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    :

% Status   : Theorem
% Rating   : 0.62 v5.3.0, 0.70 v5.2.0, 0.67 v5.1.0
% Syntax   : Number of formulae    :    2 (   0 unit;   1 type)
%            Number of atoms       :    8 (   2 equality)
%            Maximal formula depth :    8 (   6 average)
%            Number of connectives :    5 (   0   ~;   1   |;   2   &)
%                                         (   1 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    1 (   1   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    6 (   3 propositional; 0-2 arity)
%            Number of functors    :    4 (   3 constant; 0-2 arity)
%            Number of variables   :    2 (   0 sgn;   1   !;   1   ?)
%            Maximal term depth    :    2 (   1 average)
%            Arithmetic symbols    :    6 (   2 pred;    1 func;    3 numbers)
% SPC      : TFF_THM_EQU_ARI

% Comments : Also a theorem for $rat and $real
%------------------------------------------------------------------------------
tff(pow2_type,type,(
    pow2: $int > $o )).

tff(pow_of_2_8,conjecture,
    ( ! [X: $int] :
        ( pow2(X)
      <=> ( X = 1
          | ( $lesseq(2,X)
            & ? [Y: $int] :
                ( $product(2,Y) = X
                & pow2(Y) ) ) ) )
   => pow2(8) )).

%------------------------------------------------------------------------------
