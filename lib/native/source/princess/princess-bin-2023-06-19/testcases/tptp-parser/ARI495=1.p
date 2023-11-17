%------------------------------------------------------------------------------
% File     : ARI495=1 : TPTP v6.0.0. Released v5.0.0.
% Domain   : Arithmetic
% Problem  : Real: (3.2 * something) + (6.8 * something else) is 10.92
% Version  : Especial.
% English  :

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Theorem
% Rating   : 0.33 v6.0.0, 0.29 v5.5.0, 0.44 v5.4.0, 0.25 v5.3.0, 0.60 v5.2.0, 0.67 v5.1.0, 0.80 v5.0.0
% Syntax   : Number of formulae    :    1 (   1 unit;   0 type)
%            Number of atoms       :    1 (   1 equality)
%            Maximal formula depth :    3 (   3 average)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    0 (   0   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    2 (   1 propositional; 0-2 arity)
%            Number of functors    :    5 (   3 constant; 0-2 arity)
%            Number of variables   :    2 (   0 sgn;   0   !;   2   ?)
%            Maximal term depth    :    3 (   2 average)
%            Arithmetic symbols    :    6 (   1 pred;    2 func;    3 numbers)
% SPC      : TF0_THM_EQU_ARI

% Comments :
%------------------------------------------------------------------------------
tff(real_combined_problem_10,conjecture,(
    ? [X: $real,Y: $real] : $sum($product(3.2,X),$product(6.8,Y)) = 10.92 )).
%------------------------------------------------------------------------------
