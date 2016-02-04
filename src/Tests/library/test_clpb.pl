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

:- module(test_clpb,
	  [ test_clpb/0
	  ]).


:- use_module(library(plunit)).
:- use_module(library(clpb)).

test_clpb :-
	run_tests([  clpb
		  ]).

:- begin_tests(clpb).


sat(_)  --> [].
sat(X*Y) --> [_], sat(X), sat(Y).
sat(X+Y) --> [_], sat(X), sat(Y).
sat(X#Y) --> [_], sat(X), sat(Y).

vs_eqs(Vs, Eqs) :- phrase(vs_eqs(Vs), Eqs).

vs_eqs([]) --> [].
vs_eqs([V|Vs]) --> vs_eqs_(Vs, V), vs_eqs(Vs).

vs_eqs_([], _) --> [].
vs_eqs_([V|Vs], X) --> vs_eqs_(Vs, X), ( [X=V] ; [] ).

run(N) :-
       between(0,1,Done),
        length(Ls, N),
        % portray_clause(N),
        phrase(sat(Sat), Ls),
        term_variables(Sat, Vs0),
        permutation(Vs0, Vs),
        vs_eqs(Vs, Eqs),
        findall(Vs, (sat(Sat),maplist(call, Eqs),labeling(Vs)), Sols1),
        findall(Vs, (labeling(Vs),maplist(call,Eqs),sat(Sat)), Sols2),
        (   sort(Sols1, Sols), sort(Sols2, Sols) -> true
        ;   throw(neq-Sat-Eqs-Vs0-Vs-Sols1-Sols2)
        ),
        Done=1,!.


test(clpb1):- run(1).
test(clpb2):- run(2).
% most failures would happen with 3 or more involved but takes time!
% test(clpb3):- run(3).



:- end_tests(clpb).


