% Verify Proof.
verify(InputFileName):- 
    see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof).

% Check if proof is valid.
valid_proof(Prems, Goal, Proof):-
    last(Proof,Last),
    [_,Goal,_] = Last, % Last element must be goal and cannot be a list.
    [_,_,assumption] \= Last, % Last element cannot be an assumption.
    run(Prems, Proof, []).
    
% Base.
run(_, [], _).
    
% Evaluate.
run(Prems, [Row|Proof], Scope):-
    rule(Prems, Scope, Row),
    run(Prems, Proof, [Row|Scope]). % Next row.

% New Box.
run(Prems, [[H|Box]|Rest], Scope):-
    is_list(H),
    [_,_,assumption] = H, % New box must start with assumption.
    run(Prems, Box, [H|Scope]), % Append assumption directly to box scope and open box.
    % Last element from box.
    last([H|Box], LastInBox),
    run(Prems, Rest, [[LastInBox,H]|Scope]). % Continue.

% Rules.
rule(Prems, Scope, [_, Res, premise]):- member(Res, Prems).

rule(Prems, Scope, [_, Res, copy(X)]):- member([X, Res, _], Scope).

rule(Prems, Scope, [_, and(A,B), andint(X,Y)]):-
    member([X, A, _], Scope), member([Y, B, _], Scope).

rule(Prems, Scope, [_, A, andel1(X)]):- member([X, and(A,_), _], Scope).

rule(Prems, Scope, [_, B, andel2(X)]):- member([X, and(_,B), _], Scope).

rule(Prems, Scope, [_, or(A,_), orint1(X)]):- member([X, A, _], Scope).

rule(Prems, Scope, [_, or(_,B), orint2(X)]):- member([X, B, _], Scope).

rule(Prems, Scope, [_, A, orel(X,Y,U,V,W)]):- 
    member([X, or(B,C), _], Scope),
    verifyBox(Scope, [Y,B,_], [U,A,_]),
    verifyBox(Scope, [V,C,_], [W,A,_]).

rule(Prems, Scope, [_, imp(A,B), impint(X,Y)]):- 
    verifyBox(Scope,[X,A,_],[Y,B,_]).

rule(Prems, Scope, [_, B, impel(X,Y)]):-
    member([Y, imp(A,B), _], Scope), member([X, A, _], Scope).

rule(Prems, Scope, [_, neg(A),negint(X,Y)]):-
    verifyBox(Scope, [X,A,_], [Y,cont,_]).

rule(Prems, Scope, [_, cont, negel(X,Y)]):- 
    member([X, A, _], Scope), member([Y, neg(A), _], Scope).

rule(Prems, Scope, [_, A, contel(X)]):- member([X, cont, _], Scope).

rule(Prems, Scope, [_, neg(neg(A)), negnegint(X)]):- member([X, A, _], Scope).

rule(Prems, Scope, [_, A, negnegel(X)]):- member([X, neg(neg(A)), _], Scope).

rule(Prems, Scope, [_, neg(A), mt(X,Y)]):- 
    member([X, imp(A,B), _], Scope), member([Y, neg(B), _], Scope).

rule(Prems, Scope, [_, A, pbc(X,Y)]):- 
    verifyBox(Scope, [X,neg(A),_], [Y,cont,_]).

rule(Prems, Scope, [_, or(A, neg(A)), lem]).

% See if first element and last element in box matches.
% We have to switch X to Y because the list is reversed on append in run.
verifyBox([[Y|Tail]|B], X, Y):- last(Tail, X).
verifyBox([_|B], X, Y):- verifyBox(B, X, Y).
