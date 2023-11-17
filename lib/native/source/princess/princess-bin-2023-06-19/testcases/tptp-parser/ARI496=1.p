%------------------------------------------------------------------------------
% File     : ARI496=1 : TPTP v5.3.0. Released v5.0.0.
% Domain   : Arithmetic
% Problem  : Mixed: 6 is an integer
% Version  : Especial.
% English  :

% Refs     :
% Source   : [TPTP]
% Names    :

% Status   : Theorem
% Rating   : 0.25 v5.3.0, 0.29 v5.2.0, 0.40 v5.1.0, 0.50 v5.0.0
% Syntax   : Number of formulae    :    1 (   1 unit;   0 type)
%            Number of atoms       :    1 (   0 equality)
%            Maximal formula depth :    1 (   1 average)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    0 (   0   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    1 (   0 propositional; 1-1 arity)
%            Number of functors    :    1 (   1 constant; 0-0 arity)
%            Number of variables   :    0 (   0 sgn;   0   !;   0   ?)
%            Maximal term depth    :    1 (   1 average)
%            Arithmetic symbols    :    2 (   1 pred;    0 func;    1 numbers)
% SPC      : TFF_THM_NEQ_ARI

% Comments :
%------------------------------------------------------------------------------
tff(mixed_types_problem_1,conjecture,(
    $is_int(6) )).
%------------------------------------------------------------------------------
