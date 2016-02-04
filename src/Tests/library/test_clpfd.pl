/*  $Id$

    Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        wielemak@science.uva.nl
    WWW:           http://www.swi-prolog.org
    Copyright (C): 2008, University of Amsterdam

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    as published by the Free Software Foundation; either version 2
    of the License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

    As a special exception, if you link this library with other files,
    compiled with a Free Software compiler, to produce an executable, this
    library does not by itself cause the resulting executable to be covered
    by the GNU General Public License. This exception does not however
    invalidate any other reasons why the executable file might be covered by
    the GNU General Public License.
*/

:- module(test_clpfd,
	  [ test_clpfd/0
	  ]).


:- use_module(library(plunit)).
:- use_module(library(clpfd)).

test_clpfd :-
	run_tests([ clpfd_wrong,
                     clpfd_shower,
                     clpfd_num2

		  ]).

:- begin_tests(clpfd_wrong).


sat(X) :- X in 0..5.

num(L) :-
    solve(As,Bs,Cs,Ds),
    append([As,Bs,Cs,Ds], Vs),
    findall(., labeling([ff], Vs), Ls),
    length(Ls, L).

solve([A1,A2,A3,A4],[B1,B2,B3,B4],[C1,C2,C3,C4],[D1,D2,D3,D4]) :-
    maplist(sat, [A1,A2,A3,A4,B1,B2,B3,B4,C1,C2,C3,C4,D1,D2,D3,D4]),
    A1 #=< D4,
    A1 #=< D1,
    A1 + A2 + A3 + A4 #= B1 + B2 + B3 + B4,
    A1 + A2 + A3 + A4 #= C1 + C2 + C3 + C4,
    A1 + A2 + A3 + A4 #= D1 + D2 + D3 + D4,
    A1 + A2 + A3 + A4 #= A1 + B1 + C1 + D1,
    A1 + B1 + C1 + D1 #= A2 + B2 + C2 + D2,
    A1 + B1 + C1 + D1 #= A3 + B3 + C3 + D3,
    A1 + B1 + C1 + D1 #= A4 + B4 + C4 + D4,
    A1 + A2 + A3 + A4 #= A1 + B2 + C3 + D4,
    A1 + B2 + C3 + D4 #= A4 + B3 + C2 + D1.


test(wrong1):- \+
    (solve(As,Bs,Cs,Ds),
        append([As,Bs,Cs,Ds], Vs),
    Vs = [0,2,4,3,4,4,1,0,5,3,0,1,0,0,4,5]).

:- end_tests(clpfd_wrong).


:- begin_tests(clpfd_num2).

sat(N,X) :- X in 0..N.

num(L):- between(3,6,N),time(num(N,L)),writeln(num(N=L)),fail.
num(N,L) :-
    solve(N,As,Bs,Cs,Ds),
    append([As,Bs,Cs,Ds], Vs),
    findall(., labeling([ff], Vs), Ls),
    length(Ls, L).

solve(N,[A1,A2,A3,A4],[B1,B2,B3,B4],[C1,C2,C3,C4],[D1,D2,D3,D4]) :-
    maplist(sat(N), [A1,A2,A3,A4,B1,B2,B3,B4,C1,C2,C3,C4,D1,D2,D3,D4]),
    A1 #=< D4,
    A1 #=< D1,
    A1 + A2 + A3 + A4 #= B1 + B2 + B3 + B4,
    A1 + A2 + A3 + A4 #= C1 + C2 + C3 + C4,
    A1 + A2 + A3 + A4 #= D1 + D2 + D3 + D4,
    A1 + A2 + A3 + A4 #= A1 + B1 + C1 + D1,
    A1 + B1 + C1 + D1 #= A2 + B2 + C2 + D2,
    A1 + B1 + C1 + D1 #= A3 + B3 + C3 + D3,
    A1 + B1 + C1 + D1 #= A4 + B4 + C4 + D4,
    A1 + A2 + A3 + A4 #= A1 + B2 + C3 + D4,
    A1 + B2 + C3 + D4 #= A4 + B3 + C2 + D1.


test(num1,X==20):- num(1,X).
test(num2,X==323):- num(2,X).
test(num3,X==2492):- num(3,X).
% 24 seconds
% test(num4,X==13240):- num(4,X).
% 60 seconds
% test(num5,X==52400):- num(5,X).

:- end_tests(clpfd_num2).

:- begin_tests(clpfd_shower).

tasks([], _, _, _, []).
tasks([S|Ss], [D|Ds], [R|Rs], ID0, [task(S,D,_,R,ID0)|Ts]) :-
        ID1 #= ID0 + 1,
        tasks(Ss, Ds, Rs, ID1, Ts).

ready(Done, Start, Duration) :- Done #>= Start+Duration.

shower(S, Done) :-
        D = [5, 3, 8, 2, 7, 3, 9, 3],
        R = [1, 1, 1, 1, 1, 1, 1, 1],
        length(D, N),
        length(S, N),
        S ins 0..100,
        Done in 0..100,
        maplist(ready(Done), S, D),
        tasks(S, D, R, 1, Tasks),
        cumulative(Tasks, [limit(3)]),
        labeling([], [Done|S]).

test(shower2,[X,Y]==[[0, 0, 0, 3, 5, 8, 5, 11], 14]):- shower(X, Y),!.

:- end_tests(clpfd_shower).



