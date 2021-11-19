partstring(A, L, R) :-      % tar emot listan
  subset(A, R),             % skickar till subset
  length(R, L).

  subset([], []).
  subset([X|A], [X|S]):-    % tar bort huvudet och skickar till part, bygger upp return med huvudet
    part(A, S).             % kallar part utan huvud
  subset([_|A], S):-        % när vi plockat fram alla substrings med huvudet plockar vi bort det, och får fram alla substrings med det andra elementet som huvud
    subset(A, S).           %

  part(_,[]).
  part([H|T],[H|T2]) :-     % part tar fram alla substrings med det senaste huvudet
    part(T,T2).             % tar fram alla prefix
