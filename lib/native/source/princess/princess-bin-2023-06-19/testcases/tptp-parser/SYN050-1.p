%--------------------------------------------------------------------------
% File     : SYN050-1 : TPTP v5.3.0. Released v1.0.0.
% Domain   : Syntactic
% Problem  : Pelletier Problem 20
% Version  : Especial.
% English  :

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
% Source   : [Pel86]
% Names    : Pelletier 20 [Pel86]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.3.0, 0.05 v5.2.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    5 (   0 non-Horn;   3 unit;   4 RR)
%            Number of atoms       :    9 (   0 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    4 (   0 propositional; 1-1 arity)
%            Number of functors    :    3 (   2 constant; 0-2 arity)
%            Number of variables   :    6 (   4 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    ( ~ big_p(Y)
    | ~ big_q(Z)
    | big_r(f(Y,Z)) )).

cnf(clause_2,negated_conjecture,
    ( ~ big_p(Y)
    | ~ big_q(Z)
    | big_s(X) )).

cnf(clause_3,negated_conjecture,
    ( big_p(a) )).

cnf(clause_4,negated_conjecture,
    ( big_q(b) )).

cnf(clause_5,negated_conjecture,
    ( ~ big_r(W) )).

%--------------------------------------------------------------------------


