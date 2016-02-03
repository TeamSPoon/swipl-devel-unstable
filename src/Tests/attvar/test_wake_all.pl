

/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
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

:- module(test_wake_all,
	  [ test_wake_all/0
	  ]).


test_wake_all:verify_attributes(Var,_,
  [flag(test_wake,B,B),
  C is N\/B,
  flag(test_wake,_,C)]):-
  get_attr(Var,test_wake_all,N).

reset_test_wake_all:-flag(test_wake_all,_,0).
wake_all_result(N):-flag(test_wake_all,N,N).

wake(Var,N):- put_attr(Var,test_wake_all,N).


wake(1) :- wake(A,1), wake(A,2), wake_all_result(0).

va_test:verify_attributes(Var,_,[]):-get_attr(Var,va_test,Val),must_be(var,Val).

wake(2) :- put_attr(X,va_test,Y), t(X,Y)=t(1,1).

wake(3) :- wake(A,1), wake(B,2), A=a, A=B, wake_all_result(3).

/* This test has failed for several years in swi-prolog but not in yap, xsb or sicstus - still not fixed in
   backport_of_last_known_good or master (however fixed in eclipse_c and minimal_again ) */

/*
wake(6) :-
	wake(A,1), wake(B,2), A=B, A=a, wake_all_result(3).
*/


:- dynamic
	failed/1.

test_wake_all :-!.

test_wake_all :-
	retractall(failed(_)),
	forall(clause(wake(N), _, _),
        (reset_test_wake_all,        
	       (   wake(N)
	       ->  true
	       ;   format('~NFailed: ~w~n', [wake(N)]),
		   assert(failed(N))
	       ))),
	\+ failed(_).

