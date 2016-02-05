% Tabling is also important for the memoisation it offers.
% The standard example is calculating Fibonacci numbers.
%
% As an example, this benchmark calculates the N-th Fibonacci number without tabling.
% You can compare its execution time to the version with tabling in fib-no-tabling-hprolog.pl
%
% This is also interesting for a paper (Marko, Tom).

% :-table fib/2.

:- ['./tabling.pl'].

go :- 
    N = 1000,
    write('OK, N = '), writeln(N),
    cputime(Start),
    fib(N, Fib), 
    cputime(End),
    write('Fib of '), write(N), write(' is '), write(Fib),nl,
    T is End-Start,
    write('% 1000fib-hprolog.pl: execution time ='), write(T), write(' milliseconds'),nl.

fib(X,Y) :-
  start_tabling(fib(X,Y),fib_aux(X,Y)).

fib_aux(0, 1):-!.
fib_aux(1, 1):-!.
fib_aux(N,F):-N>1,N1 is N-1, N2 is N-2,fib(N1,F1),fib(N2,F2),F is F1+F2.
