
:- table c/1.
%:- import format/2 from format.

go :-
  cputime(Start),
  c(_X),
  cputime(End),
  T is End, % !
  write('% 20000shuttle-yap.pl: execution time ='), write(T), write(' milliseconds'),nl.

print_solutions :-
  c(X),
  format('YAPsol c(~w)~n',[X]),
  fail.

    c(X) :- c(Y), 0 =< Y, Y < 20000, X is -Y-1.
    c(X) :- c(Y), -20000 < Y, Y =< 0, X is -Y+1.
    c(0).
    

cputime(TimeFromLastCall) :- 
  % Documentation: in milliseconds, including garbage collection and stack shifts time. 
  statistics(cputime,[_TimeSinceBoot,TimeFromLastCall]).
