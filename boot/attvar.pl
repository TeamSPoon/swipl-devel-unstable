/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (C): 2004-2013, University of Amsterdam
			      VU University Amsterdam

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

:- module('$attvar',
	  [ '$wakeup'/1,		% +Wakeup list
	    freeze/2,			% +Var, :Goal
	    frozen/2,			% @Var, -Goal
	    call_residue_vars/2,        % :Goal, -Vars
	    copy_term/3                 % +Term, -Copy, -Residue
	  ]).

/** <module> Attributed variable handling

Attributed  variable  and  coroutining  support    based  on  attributed
variables. This module is complemented with C-defined predicates defined
in pl-attvar.c
*/


       /*******************************
       *         HOOK(S)             *
       *******************************/

%%	Module:verify_attributes(+Var, +Value, -Goals)
%
% Called *before* Var has actually been bound to Value. If it fails,
% the unification is deemed to have failed. It may succeed nondeterminately,
% in which case the unification might backtrack to give another answer.
% It is expected to return, in Goals, a list of goals to be called after Var has
% been bound to Value.
%
% This predicate is called on each of variables'' attributes each from their
% own Module

system:verify_attributes(_Var, _Value, []).



       /*******************************
       *         Wakeup              *
       *******************************/

%%	'$wakeup'(+List)
%
%	Called from the kernel if assignments will be made to
%	attributed variables.
%
%       Assignment happens in '$attvar_assign'/2
%
'$wakeup'(Wakes):-
        collect_all_va_goal_lists(Wakes,Goals,[]),              
        smsg(Wakes:-Goals), % usefull for seeing va groups  
        map_goals(Goals).


map_goals([]).
map_goals([G|Gs]):-
        call(G),
        map_goals(Gs).

smsg(H:-B):-!, format(user_error,'~N~p~n',[H:-B]),flush_output(user_error).
smsg(Msg):-format(user_error,'~N~q~n',[Msg]),flush_output(user_error).

%%	collect_all_va_goal_lists(+KernelWakeups,//)
%
% Run the verify_attributes/3 unify hook for attributes on Attvar
%
% This predicate deals with reserved attribute names to avoid
% the meta-call overhead.
%
collect_all_va_goal_lists([]) --> [].
collect_all_va_goal_lists(wakeup(Var, Att3s, Value, Rest)) -->
        {smsg(do_woken(Var, Att3s, Value))},
        ['$attvar_assign'(Var,Value)],
	collect_va_goal_list(Att3s, Var, Value),
        collect_all_va_goal_lists(Rest).


%%	collect_va_goal_list(+Att3s, +Var, +Value, -Goals) is nondet.
%
% Calls Module:verify_attributes/3 % On modules that had an 
% attribute at the time of the unification.
% Durring this process, modules may remove and change each others attributes
% Goals are collected per nondet success of 
collect_va_goal_list(_, Var , Value) --> {\+ attvar(Var),!,Var=Value}.
collect_va_goal_list(att(Module, _AttVal, Rest), Var, Value) -->
        { Module:verify_attributes(Var, Value, Goals) },        
        goals_with_module(Goals, Module),
        collect_va_goal_list(Rest, Var, Value).
collect_va_goal_list([],_,_) --> [].


goals_with_module([], _) --> [].
goals_with_module([G|Gs], M) -->
    {strip_module(G,_,GS),
     (G == GS -> MG = M:G ; MG = G)},
     [MG], goals_with_module(Gs, M).



%%	add_verify_to_attr_unify_hook(+Mod)
%
%	Add a call stub between attr_unify_hook/2
%		and verify_attrbutes/3.
%
%	This predicate only adds on stub per attribute name.
%
% ==
%	Mod:verify_attributes(Var,Value, [Mod:attr_unify_hook(Attr,Value)]):- 
%				get_attrs(Var,Mod,Attr)
% ==

add_verify_to_attr_unify_hook(Mod):-
	predicate_property(Mod:verify_attrbutes(_,_,_),defined),!.
add_verify_to_attr_unify_hook(Mod):-
	prolog_load_context(file, File),
	prolog_load_context(term_position, Pos),
	stream_position_data(line_count, Pos, Line),
        % multifile(Mod:(verify_attributes/3)),
        '$store_clause'('$source_location'(File, Line):
        (Mod:verify_attributes(Var,Value,[attr_unify_hook(Attr,Value)])
            :- get_attrs(Var,Mod,Attr)), File).


% Gleans needed attr_unify_hook/2 from sources (and needs to fail)
system:term_expansion(attr_unify_hook(_,_), _) :-
        prolog_load_context(module,M), 
        add_verify_to_attr_unify_hook(M),fail.
system:term_expansion(M:attr_unify_hook(_,_), _) :-
	add_verify_to_attr_unify_hook(M),fail.



/* "Cleanup Prolog part in boot/attvar.pl, including proper handling of freeze. Possibly move that out."
  Freeze Below is to be moved out to a differnt file .. 
  For a short day or so we
  have it converted to attr_unify_hook/2 as our 
  first case of the above stub */

verify_attributes(Var,Value,[freeze_attr_unify_hook(Goal, Value)]):-   get_attr(Val, freeze, Goal).

freeze_attr_unify_hook(Goal, Y) :- !,
	(   attvar(Y)
	->  (   get_attr(Y, freeze, G2)
	    ->	put_attr(Y, freeze, '$and'(G2, Goal))
	    ;	put_attr(Y, freeze, Goal)
	    )
	;   unfreeze(Goal)
	).


%%	unfreeze(+ConjunctionOrGoal)
%
%	Handle  unfreezing  of  conjunctions.  As  meta-calling  control
%	structures is slower than meta-interpreting them   we do this in
%	Prolog. Another advantage is that   having unfreeze/1 in between
%	makes the stacktrace and profiling   easier  to intepret. Please
%	note that we cannot use a direct conjunction as this would break
%	freeze(X, (a, !, b)).

unfreeze('$and'(A,B)) :- !,
	unfreeze(A),
	unfreeze(B).
unfreeze(Goal) :-
	Goal.

%%	freeze(@Var, :Goal)
%
%	Suspend execution of Goal until Var is unbound.

:- meta_predicate
	freeze(?, 0).

freeze(Var, Goal) :-
	'$freeze'(Var, Goal), !.	% Succeeds if delayed
freeze(_, Goal) :-
	Goal.

%%	frozen(@Var, -Goals)
%
%	Unify Goals with the goals frozen on Var or true if no
%	goals are grozen on Var.

frozen(Var, Goals) :-
	get_attr(Var, freeze, Goals0), !,
	make_conjunction(Goals0, Goals).
frozen(_, true).

make_conjunction('$and'(A0, B0), (A, B)) :- !,
	make_conjunction(A0, A),
	make_conjunction(B0, B).
make_conjunction(G, G).


		 /*******************************
		 *	       PORTRAY		*
		 *******************************/

%%	portray_attvar(@Var)
%
%	Called from write_term/3 using the option attributes(portray) or
%	when the prolog flag write_attributes   equals portray. Its task
%	is the write the attributes in a human readable format.

:- public
	portray_attvar/1.

portray_attvar(Var) :-
	write('{'),
	get_attrs(Var, Attr),
	portray_attrs(Attr, Var),
	write('}').

portray_attrs([], _).
portray_attrs(att(Name, Value, Rest), Var) :-
	portray_attr(Name, Value, Var),
	(   Rest == []
	->  true
	;   write(', '),
	    portray_attrs(Rest, Var)
	).

portray_attr(freeze, Goal, Var) :- !,
	format('freeze(~w, ~W)', [ Var, Goal,
				   [ portray(true),
				     quoted(true),
				     attributes(ignore)
				   ]
				 ]).
portray_attr(Name, Value, Var) :-
	G = Name:attr_portray_hook(Value, Var),
	(   '$c_current_predicate'(_, G),
	    G
	->  true
	;   format('~w = ...', [Name])
	).


		 /*******************************
		 *	    CALL RESIDUE	*
		 *******************************/

%%	call_residue_vars(:Goal, -Vars)
%
%	If Goal is  true,  Vars  is   the  set  of  residual  attributed
%	variables created by Goal. Goal  is   called  as in call/1. This
%	predicate  is  for  debugging  constraint   programs.  Assume  a
%	constraint program that creates  conflicting   constraints  on a
%	variable that is not part of the   result  variables of Goal. If
%	the solver is powerful enough it   will  detect the conflict and
%	fail. If the solver is too  weak   however  it  will succeed and
%	residual attributed variables holding the conflicting constraint
%	form a witness of this problem.

:- meta_predicate
	call_residue_vars(0, -).

call_residue_vars(Goal, Vars) :-
	prolog_current_choice(Chp),
	setup_call_cleanup(
	    '$call_residue_vars_start',
	    run_crv(Goal, Chp, Vars, Det),
	    '$call_residue_vars_end'),
	(   Det == true
	->  !
	;   true
	).
call_residue_vars(_, _) :-
	fail.

run_crv(Goal, Chp, Vars, Det) :-
	call(Goal),
	deterministic(Det),
        '$attvars_after_choicepoint'(Chp, Vars).

%%	copy_term(+Term, -Copy, -Gs) is det.
%
%	Creates a regular term Copy  as  a   copy  of  Term (without any
%	attributes), and a list Gs of goals that when executed reinstate
%	all attributes onto Copy. The nonterminal attribute_goals//1, as
%	defined in the modules the  attributes   stem  from,  is used to
%	convert attributes to lists of goals.

copy_term(Term, Copy, Gs) :-
	term_attvars(Term, Vs),
	(   Vs == []
	->  Gs = [],
	    copy_term(Term, Copy)
	;   findall(Term-Gs,
		    ( phrase(attvars_residuals(Vs), Gs),
		      delete_attributes(Term)
		    ),
		    [Copy-Gs])
	).

attvars_residuals([]) --> [].
attvars_residuals([V|Vs]) -->
	(   { get_attrs(V, As) }
	->  attvar_residuals(As, V)
	;   []
	),
	attvars_residuals(Vs).

attvar_residuals([], _) --> [].
attvar_residuals(att(Module,Value,As), V) -->
	(   { nonvar(V) }
	->  % a previous projection predicate could have instantiated
	    % this variable, for example, to avoid redundant goals
	    []
	;   (	{ Module == freeze }
	    ->	frozen_residuals(Value, V)
	    ;	{ current_predicate(Module:attribute_goals//1) }
	    ->	{ phrase(Module:attribute_goals(V), Goals) },
		list(Goals)
	    ;	[put_attr(V, Module, Value)]
	    )
	),
	attvar_residuals(As, V).

list([])     --> [].
list([L|Ls]) --> [L], list(Ls).

delete_attributes(Term) :-
	term_attvars(Term, Vs),
	delete_attributes_(Vs).

delete_attributes_([]).
delete_attributes_([V|Vs]) :-
	del_attrs(V),
	delete_attributes_(Vs).


%%	frozen_residuals(+FreezeAttr, +Var)// is det.
%
%	Instantiate  a  freeze  goal  for  each    member  of  the  $and
%	conjunction. Note that we cannot  map   this  into a conjunction
%	because  freeze(X,  a),  freeze(X,  !)  would  create  freeze(X,
%	(a,!)),  which  is  fundamentally  different.  We  could  create
%	freeze(X,  (call(a),  call(!)))  or  preform  a  more  eleborate
%	analysis to validate the semantics are not changed.

frozen_residuals('$and'(X,Y), V) --> !,
	frozen_residuals(X, V),
	frozen_residuals(Y, V).
frozen_residuals(X, V) -->
	[ freeze(V, X) ].



