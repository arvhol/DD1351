% beviskoll.pl
verify(InputFileName) :- see(InputFileName),
                         read(Prems), read(Goal), read(Proof),
                         seen,
                         valid_proof(Prems, Goal, Proof).

valid_proof(Prems, Goal, Proof) :-
  check_rule(Prems, Goal, Proof, []).

% När bevislistan är tom, jämför sista resultatet som testades med målet.
check_rule(Prems, Goal, [], [[Linum,Res]|Prev]) :-
  Goal == Res.

% Om regeln som använts är "premise" ska resultatet finnas i listan med premisser.
% Hitta ett element i Proof som innehåller premise.
check_rule(Prems, Goal, [[Linum, Res, premise]|Tproof], Prev) :-
  % Finns resultatet i premisslistan.
  member(Res, Prems),
  % Gå till nästa rad i beviset genom att skicka med svansen från bevislistan
  % och lägg till den bekräftade raden i Prev
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% andint
check_rule(Prems, Goal, [[Linum, Res, andint(X,Y)]|Tproof], Prev) :-
  % Hitta det första elementet på rad X och det andra elementet på rad Y
  member([X,Z1], Prev),
  member([Y,Z2], Prev),
  % Kolla om elementen vi hittat på rad X och Y är samma som finns på den
  % aktuella raden.
  and(Z1,Z2) == Res,
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% andel
check_rule(Prems, Goal, [[Linum, Res, andel1(X)]|Tproof], Prev) :-
  % Hitta en and() på rad X där första elementet är Res
  member([X, and(Res, Z)], Prev),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

check_rule(Prems, Goal, [[Linum, Res, andel2(X)]|Tproof], Prev) :-
  % Hitta en and() på rad X där andra elementet är Res
  member([X, and(Z, Res)], Prev),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% orint
check_rule(Prems, Goal, [[Linum, or(Z,W), orint1(X)]|Tproof], Prev) :-
  % Om det finns ett element Z på rad X stämmer det.
  member([X,Z],Prev),
  check_rule(Prems, Goal, Tproof, [[Linum,or(Z,W)]|Prev]).

check_rule(Prems, Goal, [[Linum, or(Z,W), orint2(X)]|Tproof], Prev) :-
  % Om det finns ett element W på rad X stämmer det.
  member([X,W],Prev),
  check_rule(Prems, Goal, Tproof, [[Linum,or(Z,W)]|Prev]).

% impel
check_rule(Prems, Goal, [[Linum, Res, impel(X,Y)]|Tproof], Prev) :-
  % Hitta elementet Z på rad X
  member([X,Z], Prev),
  % På rad Y ska det finns en imp() där Z implicerar resultatet
  member([Y,imp(Z, Res)], Prev),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% negel
check_rule(Prems, Goal, [[Linum, Res, negel(X,Y)]|Tproof], Prev) :-
  % Hitta elementet Z på rad X
  member([X,Z], Prev),
  % Finns neg av Z på rad Y
  member([Y,neg(Z)], Prev),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% contel (contradiction)
check_rule(Prems, Goal, [[Linum, Res, contel(X)]|Tproof], Prev) :-
  % Finns det en motsägelse på rad X
  member([X,cont], Prev),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% negnegint
check_rule(Prems, Goal, [[Linum,neg(neg(Z)),negnegint(X)]|Tproof], Prev) :-
  % Finns det ett Z på rad X
  member([X,Z], Prev),
  check_rule(Prems, Goal, Tproof, [[Linum, neg(neg(Z))]|Prev]).

% negnegel
check_rule(Prems, Goal, [[Linum, Res, negnegel(X)]|Tproof], Prev) :-
  % Finns det negneg av Res på rad X
  member([X,neg(neg(Res))], Prev),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% mt (modus tonem)
check_rule(Prems, Goal, [[Linum, neg(Z), mt(X,Y)]|Tproof], Prev) :-
  % Hitta Z -> W på rad X
  member([X,imp(Z, W)], Prev),
  % Finns neg W på rad Y
  member([Y,neg(W)], Prev),
  check_rule(Prems, Goal, Tproof, [[Linum,neg(Z)]|Prev]).

% lem
check_rule(Prems, Goal, [[Linum, or(Z,neg(Z)), lem]|Tproof], Prev) :-
  check_rule(Prems, Goal, Tproof, [[Linum, or(Z,neg(Z))]|Prev]).

% copy
check_rule(Prems, Goal, [[Linum, Res, copy(X)]|Tproof], Prev) :-
  % Finns Res på rad X
  member([X, Res], Prev),
  check_rule(Prems, Goal, Tproof, [[Linum,Res]|Prev]).

% ----------------- box handler ---------------------
% Hitta boxen genom att leta efter första raden, ett antagande.
check_rule(Prems, Goal, [[[Linum, Res, assumption]|Tbox]|Tproof], Prev) :-
  % Eftersom att vårat basfall alltid kollar om målet är uppfyllt hittar vi det sista
  % elementet i boxen och använder det som mål.
  last([[Linum, Res, assumption]|Tbox], [_, BoxGoal, _]),
  % Vi skickar en boxen som ett nytt bevis i för att kontrollera alla rader,
  % första raden stoppas i Prev listan.
  check_rule(Prems, BoxGoal, Tbox, [[Linum,Res]|Prev]),
  % Sätter hela boxen i Prev listan som ett element
  check_rule(Prems, Goal, Tproof, [[[Linum, Res, assumption]|Tbox]|Prev]).

% ----------------- box rules ----------------------
% impint
check_rule(Prems, Goal, [[Linum, imp(Z,W), impint(X,Y)]|Tproof], Prev) :-
  % Hämta boxen som börjar på rad X från Prev
  extBox(X, Prev, Box),
  % Finns Z på första raden och är det ett antagande
  member([X, Z, assumption], Box),
  % Finns W på sista raden, rad Y
  member([Y, W, _],Box),
  check_rule(Prems, Goal, Tproof, [[Linum, imp(Z,W)]|Prev]).

% negint
check_rule(Prems, Goal, [[Linum, neg(Z), negint(X,Y)]|Tproof], Prev) :-
  % Hämta boxen som börjar på X från Prev
  extBox(X, Prev, Box),
  % Börjar boxen med Z på rad X
  member([X, Z, _], Box),
  % Slutar boxen med en motsägelse på rad Y
  member([Y, cont, _], Box),
  check_rule(Prems, Goal, Tproof, [[Linum, neg(Z)]|Prev]).

% pbc
check_rule(Prems, Goal, [[Linum, Res, pbc(X,Y)]|Tproof], Prev) :-
  % Hämta boxen som börjar på X från Prev
  extBox(X, Prev, Box),
  % Börjar boxen med neg Res på rad X, och är det ett antagande
  member([X, neg(Res), assumption], Box),
  % Slutar boxen på rad Y  med en motsägelse
  member([Y, cont, _], Box),
  check_rule(Prems, Goal, Tproof, [[Linum, Res]|Prev]).

% orel
% X1 raden för or
% X2-X3 Box1
% X4-X5 Box2
check_rule(Prems, Goal, [[Linum, Res, orel(X1,X2,X3,X4,X5)]|Tproof], Prev) :-
  % Finns det en or på rad X och vad innehåller den
  member([X1, or(Z,W)], Prev),
  % Hämta den första boxen
  extBox(X2, Prev, Box1),
  % Börjar första boxen med Z på rad X2
  member([X2, Z, assumption], Box1),
  % Slutar första boxen med Res  på rad X3
  member([X3, Res, _], Box1),
  % Samma för andra boxen
  extBox(X4, Prev, Box2),
  member([X4, W, assumption], Box2),
  member([X5, Res, _], Box2),
  check_rule(Prems, Goal, Tproof, [[Linum, Res]|Prev]).

% -------------------- box helper -------------------
% Söker efter en specifik box i Prev med hjälp av radnummer
% Anta att boxen är huvudet i Prev
extBox(Linum, [Box|_], Box) :-
  % Har huvudet i Prev ett element med rätt radnummer och ett antagande
  member([Linum,_,assumption], Box).

% Om elementet i Prev inte var boxen som söktes försöker vi igen
extBox(Linum, [_|Tbox], _) :-
  % Ta bor huvudet, gå till nästa element
  extBox(Linum, Tbox, _).
