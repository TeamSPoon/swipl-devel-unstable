:- ['tabling.pl','testlib.pl','table_print.pl'].
% :- use_module(library(format)).

go :- 
  cputime(Start),
  d(_X),
  cputime(End),
  T is End-Start,
  write('% 10kpingpong-hprolog.pl: execution time ='), write(T), write(' milliseconds'),nl.

variant_for_xsb_comparison(d(_)).
variant_for_xsb_comparison(e(_)).

% Two mutually recursive predicates:
% d(X) :- e(Y), Y < 5, X is Y + 1.
% d(0).
%
% e(X) :- d(Y), Y < 5, X is Y + 1.
% e(0).

d(X) :-
  start_tabling(d(X),d_aux(X)).

e(X) :-
  start_tabling(e(X),e_aux(X)).

d_aux(X) :- e(Y), Y < 10000, X is Y + 1.
d_aux(0).

e_aux(X) :- d(Y), Y < 10000, X is Y + 1.
e_aux(0).
