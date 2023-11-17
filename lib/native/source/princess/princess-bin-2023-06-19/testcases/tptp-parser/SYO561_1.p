%------------------------------------------------------------------------------
% File     : SYO561_1 : TPTP v5.4.0. Released v5.3.0.
% Domain   : Syntactic
% Problem  : Distinct objects
% Version  : Biased.
% English  : 

% Refs     : 
% Source   : TPTP
% Names    : 

% Status   : Theorem
% Rating   : 0.75 v5.4.0, 0.67 v5.3.0
% Syntax   : Number of formulae    :    5 (   5 unit;   3 type)
%            Number of atoms       :    5 (   1 equality)
%            Maximal formula depth :    2 (   2 average)
%            Number of connectives :    1 (   1   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    0 (   0   >;   0   *;   0   +;   0  <<)
%            Number of predicates  :    6 (   4 propositional; 0-2 arity)
%            Number of functors    :    2 (   2 constant; 0-0 arity)
%            Number of variables   :    0 (   0 sgn;   0   !;   0   ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : TFF_THM_EQU_NAR

% Comments : Designed to test if systems have implemented $distinct.
%------------------------------------------------------------------------------
tff(company_type,type,(
    company: $tType )).

tff(apple_company,type,(
    apple: company )).

tff(microsoft_company,type,(
    microsoft: company )).

tff(distinct_companies,axiom,(
    $distinct(apple,microsoft) )).

tff(apple_not_microsoft,conjecture,(
    apple != microsoft )).

%------------------------------------------------------------------------------
