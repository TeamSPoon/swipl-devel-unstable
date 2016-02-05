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


:- table c/1.
%:- import format/2 from format.

go :-
  cputime(Start),
  c(_X),
  cputime(End),
  T is (End-Start),
  write('% 50000shuttle-caio.pl: execution time ='), write(T), write(' milliseconds'),nl.

print_solutions :-
  c(X),
  format('CAIOsol c(~w)~n',[X]),
  fail.

    c(X) :- c(Y), 0 =< Y, Y < 50000, X is -Y-1.
    c(X) :- c(Y), -50000 < Y, Y =< 0, X is -Y+1.
    c(0).
    
