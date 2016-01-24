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
	  [ undo/1,                     % :Goal
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

%%	unify(Atts, Next, Var, Value)
%
%	Called from the kernel if assignments will be made to attributed
%	variables.
%
%       Assignment happens in 'pre_unify'/4

:- module_transparent(system:unify/4).
:- module_transparent(system:pre_unify/4).
:- module_transparent(system:post_unify/4).
:- module_transparent(system:other_unify/5).
:- module_transparent(system:ifdef/2).

system:ifdef(IfDef,Else):-'$c_current_predicate'(_, IfDef)->IfDef;Else.

system:unify(Atts, Next, Var, Value):-
   (attvar(Var)
    -> user:pre_unify(Atts,'$attvar_assign'(Var,Value), Var, Value);
     true),
     user:post_unify(Atts, Next, Var, Value).

           /*******************************
           *	  VERIFY ATTRIBUTES	* 
           *******************************/

%%	pre_unify(+Att3s, +Next, +Var, +Value)
%
%	Called from the kernel if assignments will be made to attributed
%	variables.
%
%	First calls Module:verify_attributes/3 for each `Module` for which Var
%	has an attribute. During this process,   modules  may remove and
%	change each others attributes.
%
%	Next bind the Var to Value
%
%	Finally call post binding closures/hooks.

system:pre_unify(att(Module, _AttVal, Rest), Next, Var, Value):- !,
        ifdef(Module:verify_attributes(Var, Value, Goals),Goals=[]),
        system:pre_unify(Rest, Next, Var, Value),
        goals_with_module(Goals,Module).

system:pre_unify(_, Next,Var, Value):- attvar(Value),
        get_attrs(Value,Atts),!,
        system:other_unify(Atts,Next,Value, Var, Goals),
        Goals.

system:pre_unify(_, Next,_, _):- call(Next).


system:goals_with_module([G|Gs], M):- !,
        M:call(G),
	system:goals_with_module(Gs, M).
system:goals_with_module(_,_).


/* this is for reflexive non-assignment peer pre_unify */
system:other_unify(att(Module, _AttVal, Rest), Next, Var, Value,(Module:goals_with_module(Goals,Module),G)):- !,
        system:ifdef(Module:verify_attributes(Var, Value, Goals),Goals=[]),
        system:other_unify(Rest, Next, Var, Value, G).

system:other_unify(_,Next,_, _, Next).



		 /*******************************
		 *	  ATTR UNIFY HOOK	*
		 *******************************/


system:post_unify(att(Module, AttVal, Rest), Next, Var, Value) :- !,
	ifdef(Module:attr_unify_hook(AttVal, Value),true),
	system:post_unify(Rest, Next, Var, Value).
system:post_unify(_,Next,_,_):- Next.



        /***************
         *  UNDO HOOK  *
         ***************/
/*    
    ?- F='\n',undo(((writeln(F:1);writeln(F:2)),fail)),!,write(before),fail.
    BUG: ?- undo(((member(F,[1,2,3]),writeln(F),fail))),!,write(before),fail.
*/
system:'$meta'('$undo_unify', _, Goal, 1):- !, '$schedule_wakeup'(Goal).
:- meta_predicate(undo(:)).
undo(GoalIn):- 
        metaterm_options(W,W), 
        T is W \/ 0x0080, % Flag to turn on trail scanning
        ( T =:= W  
        -> GoalIn=Goal 
        ;  Goal=(metaterm_options(_,W),GoalIn)
        ),
        put_attr(Var,'$undo_unify',GoalIn),
        metaterm_options(_,T),
        '$attvar_assign'(Var,Goal).


		 /*******************************
		 *	      FREEZE		*
		 *******************************/

%%	freeze(@Var, :Goal)
%
%	Suspend execution of Goal until Var is bound.

:- meta_predicate
	freeze(?, 0).

freeze(Var, Goal) :-
	'$freeze'(Var, Goal), !.	% Succeeds if delayed
freeze(_, Goal) :-
	call(Goal).

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


freeze:attr_unify_hook(Goal, Y) :-
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
