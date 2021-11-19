node(a).
node(b).
node(c).
node(d).
node(e).

edge(a, b).
edge(a, c).
edge(b, c).
edge(c, d).
edge(d, e).

% ------------------------------------
appendEl(X, [], [X]).
appendEl(X, [H | T], [H | Y]) :-
           appendEl(X, T, Y).
% ------------------------------------

pathTo(S, D, Path):-
  path_hlp(S, D, [], Path).

path_hlp(S, S, _, [S]).

path_hlp(S, D, A, [S|Path]):-
  edge(S, M),
  \+member(M, A),
  appendEl(S, A, A2),
  path_hlp(M, D, A2, Path).
