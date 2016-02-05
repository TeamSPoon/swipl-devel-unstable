:- expects_dialect(ciao).
:- use_package(tabling).
:- use_module(library(prolog_sys)).
:- use_module(library(write)).
% :- use_module(library(format)).

cputime(T) :-
  % Not sure whether to pick walltime, runtime, usertime or systemtime
  statistics(runtime,[T,_]).

writeln(T) :-
  write(T),
  nl.

:- table d/1,e/1.
%:- import format/2 from format.

go :- 
  cputime(Start),
  d(_),
  cputime(End),
  T is ( End-Start ),
  write('% 10kpingpong-caio.pl: execution time ='), write(T), write(' milliseconds'),nl.

print_solutions :-
  d(X),
  format('CAIOsol d(~w)~n',[X]),
  fail.
print_solutions :-
  e(X),
  format('CAIOsol e(~w)~n',[X]),
  fail.


% Two mutually recursive predicates:
d(X) :- e(Y), Y < 10000, X is Y + 1.
d(0).

e(X) :- d(Y), Y < 10000, X is Y + 1.
e(0).
