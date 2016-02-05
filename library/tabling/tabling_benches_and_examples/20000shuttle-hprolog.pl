
:- ['tabling.pl','testlib.pl','table_print.pl'].
% :- use_module(library(format)).

variant_for_xsb_comparison(c(_)).

go :-
  cputime(Start),
  c(_X),
  cputime(End),
  T is (End-Start) ,
  write('% 20000shuttle-hprolog.pl: execution time ='), write(T), write(' milliseconds'),nl.

c(X) :-
  start_tabling(c(X),c_aux(X)).

c_aux(X) :- c(Y), 0 =< Y, Y < 20000, X is -Y-1.
c_aux(X) :- c(Y), -20000 < Y, Y =< 0, X is -Y+1.
c_aux(0).

