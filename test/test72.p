%--------------------------------------------------------------------------
% File     : SYN075+1 : TPTP v2.6.0. Released v2.0.0.
% Domain   : Syntactic
% Problem  : Pelletier Problem 52
% Version  : Especial.
% English  : 

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
%          : [Hah94] Haehnle (1994), Email to G. Sutcliffe
% Source   : [Hah94]
% Names    : Pelletier 52 [Pel86]

% Status   : theorem
% Rating   : 0.00 v2.5.0, 0.33 v2.4.0, 0.33 v2.2.1, 0.00 v2.1.0
% Syntax   : Number of formulae    :    7 (   1 unit)
%            Number of atoms       :   18 (  12 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   11 (   0 ~  ;   0  |;   4  &)
%                                         (   3 <=>;   4 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :   20 (   0 singleton;  16 !;   4 ?)
%            Maximal term depth    :    1 (   1 average)

% Comments : 
%--------------------------------------------------------------------------
%----Include axioms of equality
%--------------------------------------------------------------------------
%%%%%%%%%%%%%%%%%include('Axioms/EQU001+0.ax').
% File     : EQU001+0 : TPTP v2.6.0. Bugfixed v2.0.0.
% Domain   : Equality
% Axioms   : Reflexivity, symmetry and transitivity, of equality
% Version  : 
% English  : 

% Refs     : 
% Source   : [TPTP]
% Names    : 

% Status   : 
% Syntax   : Number of formulae    :    3 (   1 unit)
%            Number of atoms       :    6 (   6 equality)
%            Maximal formula depth :    4 (   3 average)
%            Number of connectives :    3 (   0 ~  ;   0  |;   1  &)
%                                         (   0 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    6 (   0 singleton;   6 !;   0 ?)
%            Maximal term depth    :    1 (   1 average)

% Comments : 
%--------------------------------------------------------------------------
input_formula(reflexivity,axiom,
    ! [X] : equal(X,X)   ).

input_formula(symmetry,axiom,
    ! [X,Y] : 
      ( equal(X,Y)
     => equal(Y,X) )   ).

input_formula(transitivity,axiom,
    ! [X,Y,Z] : 
      ( ( equal(X,Y)
        & equal(Y,Z) )
     => equal(X,Z) )   ).
%--------------------------------------------------------------------------
%--------------------------------------------------------------------------
%----Substitution axioms
input_formula(big_f_substitution_1,axiom,(
    ! [A,B,C] : 
      ( ( equal(A,B)
        & big_f(A,C) )
     => big_f(B,C) )   )).

input_formula(big_f_substitution_2,axiom,(
    ! [A,B,C] : 
      ( ( equal(A,B)
        & big_f(C,A) )
     => big_f(C,B) )   )).

%----Problem axioms
input_formula(pel52_1,axiom,(
    ? [Z,W] : 
    ! [X,Y] : 
      ( big_f(X,Y)
    <=> ( equal(X,Z)
        & equal(Y,W) ) )   )).

input_formula(pel52,conjecture,(
    ? [W] : 
    ! [Y] : 
      ( ? [Z] : 
        ! [X] : 
          ( big_f(X,Y)
        <=> equal(X,Z) )
    <=> equal(Y,W) )   )).
%--------------------------------------------------------------------------
