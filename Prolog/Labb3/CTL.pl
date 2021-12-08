% Load model, initial state and formula from file.
verify(Input) :-
    see(Input), read(T), read(L), read(S), read(F), seen,
    check(T, L, S, [], F).
% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.

% AND OR
% AX EX

% CURRENT STATE
% Literals
% P
check(_, L, S, [], X) :-
  member([S, Labels], L),     % Tar fram labels för S, dvs vad som finns i current state
  member(X, Labels).          % Kollar att X finns i labels, kollar att värdet stämmer
% NEG P
check(_, L, S, [], neg(X)) :-
  member([S, Labels], L),
  \+member(X, Labels).        % Kolla att X inte finns i labels,
                              % dvs värdet ska inte finnas där
% AND
check(T, L, S, [], and(X,Y)) :-
  check(T, L, S, [], X),      % Kollar att båda värdena existerar
  check(T, L, S, [], Y).

% OR1
check(T, L, S, [], or(X,Y)) :-
  check(T, L, S, [], X).      % Kollar att X existerar
% OR2
check(T, L, S, [], or(X,Y)) :-
  check(T, L, S, [], Y).      % Kollar att Y existerar, om X inte existerar

% AX
check(T, L, S, [], ax(X)) :-
  member([S, Adjacent], T),           % Lägg alla grannar till S i Adjacent
  checkAdjA(T, L, Adjacent, [], X).   % Kolla att alla grannar uppfyller X

% EX
check(T, L, S, [], ex(X)) :-
  member([S, Adjacent], T),           % Ta fram alla grannar till S
  checkAdjE(T, L, Adjacent, [], X).   % Kolla att någon granne uppfyller X

% AG1
check(_, _, S, U, ag(_)) :-
  member(S, U).                       % Kollar om S har blvit besökt tidigare
% AG2
check(T, L, S, U, ag(X)) :-
  \+member(S, U),                     % Kollar att S inte blivit besökt tidigare
  check(T, L, S, [], X),              % Kollar att startnoden uppfyller X
  member([S, Adj], T),                % Ta fram alla grannar
  checkAdjA(T, L, Adj, [S|U], ag(X)). % Kollar att alla grannar uppfyller ag(X),
                                      % samt lägger S i "besökslistan"
% AF1
check(T, L, S, U, af(X)) :-
  \+member(S, U),                     % Kollar att S inte finns i U, dvs är besökt
  check(T, L, S, [], X).              % Kolla att startnoden innehåller X
% AF2
check(T, L, S, U, af(X)) :-
  \+member(S, U),                     % Kollar att S inte har blivit besökt tidigare
  member([S, Adj], T),                % Ta fram grannarna
  checkAdjA(T, L, Adj, [S|U], af(X)). % Kolla att grannarna uppfyller af(X),
                                      % samt lägger S i "besökslistan"
% EG1
check(_, _, S, U, eg(_)) :-
  member(S, U).                       % Kollar om S har blivit besökt tidigare
% EG2
check(T, L, S, U, eg(X)) :-
  \+member(S, U),                     % Kollar att S inte har blivit besökt tidigare
  check(T, L, S, [], X),              % Kollar att S uppfyller X
  member([S, Adj], T),                % Ta fram grannarna
  checkAdjE(T, L, Adj, [S|U], eg(X)). % Kolla att alla grannar uppfyller eg(X),
                                      % samt lägger S i "besökslistan"
% EF1
check(T, L, S, U, ef(X)) :-
  \+member(S, U),                     % Kolla att S inte blivit besökt tidigare
  check(T, L, S, [], X).              % Kolla att S uppfyller X
% EF2
check(T, L, S, U, ef(X)) :-
  \+member(S, U),                     % Kolla att S inte blivit besökt tidigare
  member([S, Adj], T),                % Ta fram grannar
  checkAdjE(T, L, Adj, [S|U], ef(X)). % Kolla att alla grannar uppfyller ef(X),
                                      % samt lägg till S i "besökslistan"
% check if all adjacent nodes are labeled x
checkAdjA(_, _, [], _, _).          % Sluta kolla grannar när grannlistan är tom

% Eftersom att alla vägar ska uppfylla det måste hela listan med grannar uppfylla villkoret
checkAdjA(T, L, [H|Tail], U, X) :-  % Ta fram första grannen som huvud, H
  check(T, L, H, U, X),             % Kolla att H uppfyller X
  checkAdjA(T, L, Tail, U, X).      % Gå till nästa element genom att skicka vidare svansen

% check if at least one adjacent nodes is labeled x

checkAdjE(T, L, [H|Tail], U, X) :-
  check(T, L, H, U, X).             % Kollar om grannen H uppfyller X

checkAdjE(T, L, [H|Tail], U, X) :-
  checkAdjE(T, L, Tail, U, X).      % Testa nästa om huvudet inte är korrekt
