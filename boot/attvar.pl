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

/* updates to dynamic attributes:modules_with_attributes/1 happen is atts.pl */ 
:- multifile attributes:modules_with_attributes/1.
:- dynamic attributes:modules_with_attributes/1.
attributes:modules_with_attributes([]).

       /*******************************
       *         HOOKS              *
       *******************************/

system:attr_unify_hook(_AttrValue, _Value).

%%  Module:verify_attributes(+Var, +Value, -Goals)
%  
% Called *before* Var has actually been bound to Value. If it fails,
% the unification is deemed to have failed. It may succeed nondeterminately, 
% in which case the unification might backtrack to give another answer.
% It is expected to return, in Goals, a list of goals to be called after Var has
% been bound to Value.
%
%  This predicate is called in each module that contains an attribute declaration.
%
% For cases in which look like:
% ==
% mod:verify_attributes(Var,Value,[]):- get_attrs(Var,mod,Atts),some_code(Atts,Value).
% ==
% it can in some cases be more efficient to avoid this extra get_attrs/3 call.
% ==
%  mod:attr_unify_hook(Atts,Value):- some_code(Atts,Value).
% ==
%  attr_unify_hook/2 is provided by both SWI and YAP
%
system:verify_attributes(_Var, _Value, []).

%%	'$wakeup'(+List)
%
%	Called from the kernel if assignments will be made to
%	attributed variables.
%       current code requires O_VERIFY_ATTRIBUTES (In C)
%
%       Assignment happens in '$attvar_assign'/2
%

'$wakeup'([]).
'$wakeup'(wakeup(UnifyAtMod, Var, Att3s, Value, Rest)) :-
	attributes:modules_with_attributes(AttsMods), 
        '$delete'(AttsMods,UnifyAtMod,RestAttsMods),!,
	do_verify_attributes([UnifyAtMod|RestAttsMods], Var, Att3s, Value, Goals),
	(attvar(Var)->'$attvar_assign'(Var,Value);true),
        call_all_attr_uhooks(Att3s, Value),        
        '$wakeup'(Rest),
        call_goals(UnifyAtMod,Goals).
          

call_goals(_,[]):- !.
call_goals(M,(G,Gs)):- !,call_goals(M,G),call_goals(M,Gs).
call_goals(_, (M:G)):- !,call_goals(M,G).
call_goals(M,[G|Gs]):- !,call_goals(M,G),call_goals(M,Gs).
call_goals(M,G):- M:G.

%% do_verify_attributes(+AttsModules, +Var, +Att3s, +Value, -Goals) is nondet.
%
% calls  Module:verify_attributes/3 
%
%  1) Modules that have defined an attribute in Att3s
%  2) The caller''s module (Head of AttsModules)
%  3) remaining modules who have defined attributes on some variable (Tail of AttsModules)
%
%  
do_verify_attributes(_AttsModules,Var,_Att3s,_Value,[]) :- \+ attvar(Var),!.
do_verify_attributes(AttsModules,Var, att(Module, _AttVal, Rest), Value, (Module:Goals1,Goals2)) :-  !,
    Module:verify_attributes(Var, Value, Goals1),
    '$delete'(AttsModules,Module,RemainingMods),
    do_verify_attributes(RemainingMods, Var,  Rest, Value, Goals2).

% Call verify_attributes/3 in rest of modules
do_verify_attributes([],_Var, _Att3s, _Value, []):-!.
do_verify_attributes([Module|AttsModules], Var, [], Value, (Module:Goals1,Goals2)):- 
   Module:verify_attributes(Var, Value, Goals1),
   do_verify_attributes(AttsModules, Var, [], Value, Goals2).
   


call_all_attr_uhooks([], _).
call_all_attr_uhooks(att(Module, AttVal, Rest), Value) :-
	uhook(Module, AttVal, Value),
	call_all_attr_uhooks(Rest, Value).


%%	uhook(+AttributeName, +AttributeValue, +Value)
%
%	Run the unify hook for attributed named AttributeName after
%	assigning an attvar with attribute AttributeValue the value
%	Value.
%
%	This predicate deals with reserved attribute names to avoid
%	the meta-call overhead.

uhook(freeze, Goal, Y) :- !,
	(   attvar(Y)
	->  (   get_attr(Y, freeze, G2)
	    ->	put_attr(Y, freeze, '$and'(G2, Goal))
	    ;	put_attr(Y, freeze, Goal)
	    )
	;   unfreeze(Goal)
	).
uhook(Module, AttVal, Value) :-
	Module:attr_unify_hook(AttVal, Value).


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
