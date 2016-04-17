

:- if(current_predicate((topl)/1)).

:- topl((go/0, main/0)).
:- table(reach/2).

:- else.

cputime(X):- statistics(cputime,X).

:- endif.

/*


NEW SWI Tabling asserta vs recorda
TIME:9.638810966000001
TIME:13.412892943000001

OLD SWI Tabling asserta vs recorda
TIME:8.806049874
TIME:13.26628324 
*/


go:-
    (cputime(Start)),
    top,
    cputime(End),
    T is End-Start,
    write('TIME:'),write(T),nl.

main:-top.

top:-
    reach(X,Y),
   % write(X),
    fail.
top.

reach(X,Y):-edge(X,Y).
reach(X,Y):-reach(X,Z),edge(Z,Y).

:-['sg_edge.pl'].

:- time(go).
