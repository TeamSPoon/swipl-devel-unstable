/*  Part of SWI-Prolog

    Author:        Douglas Miles
    E-mail:        logicmoo@gmail.com
    WWW:           http://www.swi-prolog.org
    Copyright (C): 2008-2015, University of Amsterdam
			      VU University Amsterdam

    This library is free software; you can redistribute it and/or
    modify it under the terms of the GNU Lesser General Public
    License as published by the Free Software Foundation; either
    version 2.1 of the License, or (at your option) any later version.

    This library is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
*/

:- module(test_tabling_sanity,
	  [ test_tabling_sanity/0
	  ]).


:- discontiguous drac/1.

reset_test_tabling_sanity:-flag(test_tabling_sanity,_,0).

tabling_sanity_result(N):-flag(test_tabling_sanity,N,N).


avoids(Source,Target):-avoids0(Source,Target),\=(Source,Target).

:- discontiguous avoids0/2.
:- table avoids0/2.
avoids0(Source,Target) :- owes(Source,Target).
avoids0(Source,Target) :-
        owes(Source,Intermediate),
	avoids0(Intermediate,Target).

owes(andy,bill).
owes(bill,carl).
owes(carl,bill).



drac(1) :- findall(avoids(Source,Target),avoids(Source,Target),List),
  List==[avoids(andy, bill), avoids(bill, carl), avoids(carl, bill), avoids(andy, carl)].


:- dynamic
	failed/1.

test_tabling_sanity :-
	retractall(failed(_)),
	forall(clause(drac(N), _, _),
        (reset_test_tabling_sanity,        
	       (   drac(N)
	       ->  true
	       ;   format('~NFailed: ~w~n', [drac(N)]),
		   assert(failed(N))
	       ))),
	\+ failed(_).

