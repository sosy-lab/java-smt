%------------------------------------------------------------------------------
% File     : ARI120=1 : TPTP v5.3.0. Released v5.0.0.
% Domain   : Arithmetic
% Problem  : Integer: Product of X and X is 4
% Version  : Especial.
% English  :

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Theorem
% Rating   : 0.75 v5.3.0, 0.80 v5.2.0, 0.83 v5.1.0, 1.00 v5.0.0
% Syntax   : Number of formulae    :    2 (   0 unit;   1 type)
%            Number of atoms       :    6 (   2 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :    4 (   1   ~;   0   |;   2   &)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    1 (   1   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    5 (   3 propositional; 0-2 arity)
%            Number of functors    :    3 (   2 constant; 0-2 arity)
%            Number of variables   :    2 (   0 sgn;   0   !;   2   ?)
%            Maximal term depth    :    2 (   1 average)
%            Arithmetic symbols    :    4 (   1 pred;    1 func;    2 numbers)
% SPC      : TFF_THM_EQU_ARI

% Comments :
%------------------------------------------------------------------------------
tff(p_type,type,(
    p: $int > $o )).

tff(product_X_X_4_predicate,conjecture,
    ( p(2)
   => ? [X: $int,Y: $int] : 
        ( p(X)
        & X != Y
        & $product(Y,Y) = 4 ) )).
%------------------------------------------------------------------------------
