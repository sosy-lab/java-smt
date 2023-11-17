%------------------------------------------------------------------------------
% File     : ARI522=1 : TPTP v6.0.0. Released v5.0.0.
% Domain   : Arithmetic
% Problem  : Mixed: Sum 3.5 and 3/4 coerced to real is 4.25
% Version  : Especial.
% English  :

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Theorem
% Rating   : 0.67 v6.0.0, 0.57 v5.5.0, 0.56 v5.4.0, 0.62 v5.3.0, 0.70 v5.2.0, 0.67 v5.1.0, 0.60 v5.0.0
% Syntax   : Number of formulae    :    1 (   1 unit;   0 type)
%            Number of atoms       :    1 (   1 equality)
%            Maximal formula depth :    1 (   1 average)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    0 (   0   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    5 (   3 constant; 0-2 arity)
%            Number of variables   :    0 (   0 sgn;   0   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
%            Arithmetic symbols    :    5 (   0 pred;    2 func;    3 numbers)
% SPC      : TF0_THM_EQU_ARI

% Comments :
%------------------------------------------------------------------------------
tff(mixed_types_problem_27,conjecture,
    ( $sum(3.5,$to_real(3/4)) = 4.25 )).
%------------------------------------------------------------------------------
