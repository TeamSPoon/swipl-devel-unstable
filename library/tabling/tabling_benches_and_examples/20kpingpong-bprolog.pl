:- table d/1,e/1.
%:- import format/2 from format.

go :- 
  cputime(Start),
  d(_),
  cputime(End),
  T is ( End-Start ),
  write('% 20kpingpong-bprolog.pl: execution time ='), write(T), write(' milliseconds'),nl.

print_solutions :-
  d(X),
  format('BPsol d(~w)~n',[X]),
  fail.
print_solutions :-
  e(X),
  format('BPsol e(~w)~n',[X]),
  fail.


% Two mutually recursive predicates:
d(X) :- e(Y), Y < 20000, X is Y + 1.
d(0).

e(X) :- d(Y), Y < 20000, X is Y + 1.
e(0).
