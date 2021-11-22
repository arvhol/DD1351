% beviskoll.pl
verify(InputFileName) :- see(InputFileName),
                         read(Prems), read(Goal), read(Proof),
                         seen,
                         valid_proof(Prems, Goal, Proof).

valid_proof(Prems, Goal, Proof) :-
  check_rule(Prems, Goal, Proof, []),
  write('Slut. ').

% När bevislistan är tom, jämför sista resultatet med vårt mål.
check_rule(Prems, Goal, [], [[Linum,Res]|Prev]) :-
  Goal == Res,
  write('\nBeviset är korrekt. ').

% Premise
check_rule(Prems, Goal, [[Linum, Res, premise]|Tproof], Prev) :-
  member(Res, Prems),
  write('Premissen stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% andint
check_rule(Prems, Goal, [[Linum, Res, andint(X,Y)]|Tproof], Prev) :-
  member([X,Z1], Prev),
  member([Y,Z2], Prev),
  and(Z1,Z2) == Res,
  write('andint stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% AndEl
check_rule(Prems, Goal, [[Linum, Res, andel1(X)]|Tproof], Prev) :-
  member([X, and(Res, Z)], Prev),
  write('andel1 stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

check_rule(Prems, Goal, [[Linum, Res, andel2(X)]|Tproof], Prev) :-
  member([X, and(Z, Res)], Prev),
  write('andel2 stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% orint
check_rule(Prems, Goal, [[Linum, or(Z,W), orint1(X)]|Tproof], Prev) :-
  member([X,Z],Prev),
  write('orint1 stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum,or(Z,W)]|Prev]).

check_rule(Prems, Goal, [[Linum, or(Z,W), orint2(X)]|Tproof], Prev) :-
  member([X,W],Prev),
  write('orint2 stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum,or(Z,W)]|Prev]).

% impel
check_rule(Prems, Goal, [[Linum, Res, impel(X,Y)]|Tproof], Prev) :-
  member([X,Z], Prev),
  member([Y,imp(Z, Res)], Prev),
  write('impel stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% negel
check_rule(Prems, Goal, [[Linum, Res, negel(X,Y)]|Tproof], Prev) :-
  member([X,Z], Prev),
  member([Y,neg(Z)], Prev),
  write('negel stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% contel (contradiction)
check_rule(Prems, Goal, [[Linum, Res, contel(X)]|Tproof], Prev) :-
  member([X,cont], Prev),
  write('contel stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% negnegint
check_rule(Prems, Goal, [[Linum,neg(neg(Z)),negnegint(X)]|Tproof], Prev) :-
  member([X,Z], Prev),
  write('negnegint stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum, neg(neg(Z))]|Prev]).

% negnegel
check_rule(Prems, Goal, [[Linum, Res, negnegel(X)]|Tproof], Prev) :-
  member([X,neg(neg(Res))], Prev),
  write('negnegel stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% mt (modus tonem)
check_rule(Prems, Goal, [[Linum, neg(Z), mt(X,Y)]|Tproof], Prev) :-
  member([X,imp(Z, W)], Prev),
  member([Y,neg(W)], Prev),
  write('mt stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum,neg(Z)]|Prev]).

% lem
check_rule(Prems, Goal, [[Linum, or(Z,neg(Z)), lem]|Tproof], Prev) :-
  write('lem stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum, or(Z,neg(Z))]|Prev]).

% copy
check_rule(Prems, Goal, [[Linum, Res, copy(X)]|Tproof], Prev) :-
  member([X, Res], Prev),
  write('copy stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% ----------------- box handlers ---------------------
% impint
check_rule(Prems, Goal, [[[Linum,Res,assumption]|Tbox], [Linum2, imp(Res, Z), impint(Linum,Y)]|Tproof], Prev) :-
  check_rule([Res|Prems], Z, Tbox, [[Linum,Res]|Prev]),
  %write('2'),
  %K is Linum2 - 1,
  %member([K,Z,_], [[Linum,Res,assumption]|Tbox]),
  write('impint stämmer. '),
  check_rule(Prems, Goal, Tproof, [[Linum2,imp(Res,Z)]|Prev]).
