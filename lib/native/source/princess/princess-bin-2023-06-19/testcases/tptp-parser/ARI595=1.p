%------------------------------------------------------------------------------
% File     : ARI595=1 : TPTP v5.1.0. Released v5.1.0.
% Domain   : Arithmetic
% Problem  : There is a number in [a,...,a+2] that is divisible by 3
% Version  : Especial.
% English  :

% Refs     : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    :

% Status   : Theorem
% Rating   : 1.00 v5.1.0
% Syntax   : Number of formulae    :    3 (   1 unit;   2 type)
%            Number of atoms       :    7 (   0 equality)
%            Maximal formula depth :    5 (   3 average)
%            Number of connectives :    3 (   0   ~;   0   |;   1   &)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    1 (   1   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    6 (   4 propositional; 0-2 arity)
%            Number of functors    :    5 (   3 constant; 0-2 arity)
%            Number of variables   :    2 (   0 sgn;   1   !;   1   ?)
%            Maximal term depth    :    2 (   1 average)
%            Arithmetic symbols    :    6 (   2 pred;    2 func;    2 numbers)
% SPC      : TFF_THM_NEQ_ARI

% Comments : Also a theorem for $rat and $real, but much easier
%------------------------------------------------------------------------------
tff(p_type,type,(
    p: $int > $o )).

tff(a_type,type,(
    a: $int )).

tff(exists_X_in_a_to_aplus2_div_3,conjecture,
    ( ! [Z: $int] :
        ( ( $lesseq(a,Z)
          & $lesseq(Z,$sum(a,2)) )
       => p(Z) )
   => ? [X: $int] : p($product(3,X)) )).

%------------------------------------------------------------------------------
