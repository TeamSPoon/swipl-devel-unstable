:- table d/1,e/1.
:- import format/2 from format.

go :- 
  cputime(Start),
  d(_),
  cputime(End),
  T is ( End-Start ) * 1000,
  write('% 10kpingpong-xsb.pl: execution time ='), write(T), write(' milliseconds'),nl.

print_solutions :-
  d(X),
  format('XSBsol d(~w)~n',[X]),
  fail.
print_solutions :-
  e(X),
  format('XSBsol e(~w)~n',[X]),
  fail.


% Two mutually recursive predicates:
d(X) :- e(Y), Y < 10000, X is Y + 1.
d(0).

e(X) :- d(Y), Y < 10000, X is Y + 1.
e(0).
