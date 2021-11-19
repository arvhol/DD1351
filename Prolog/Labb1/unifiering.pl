remove_duplicates([],[]).            % basecase

remove_duplicates([X|Xs], L) :-
  % member(X,Xs),                       % finns X, dvs Head, med i Xs, dvs Tail
  select(X,Xs,Tmp),                   % om sant, ta bort element likt head från xs till tmp
  remove_duplicates([X|Tmp], L).

remove_duplicates([X|Xs], [X|L]) :-   % varje X som kommer hit
  \+member(X,Xs),
  remove_duplicates(Xs, L).           % är unikt, returna till L

%-----------------------------------------%
