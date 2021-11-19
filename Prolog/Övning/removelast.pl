removelast([X|Xs],L):-      /*rule consists of a head(predicate)*/
  rml_helper(X,Xs,L).                        /*body(predicate, predicate ...)*/
                                             /*predicate.*/
rml_helper(_,[],[]).

rml_helper(X,[X1|Xs],[X|L]):-
  rml_helper(X1,Xs,L).
