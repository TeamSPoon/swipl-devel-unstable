
:- table c/1.
:- import format/2 from format.

go :-
  cputime(Start),
  c(_X),
  cputime(End),
  T is (End-Start) * 1000,
  write('% 2000shuttle-xsb.pl: execution time ='), write(T), write(' milliseconds'),nl.

print_solutions :-
  c(X),
  format('XSBsol c(~w)~n',[X]),
  fail.

    c(X) :- c(Y), 0 =< Y, Y < 2000, X is -Y-1.
    c(X) :- c(Y), -2000 < Y, Y =< 0, X is -Y+1.
    c(0).
    
